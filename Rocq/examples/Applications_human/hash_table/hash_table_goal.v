From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.hash_table Require Import hash_table_def.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.hash_table Require Import hash_table_lib.
Local Open Scope sac.

(*----- Function entails_emp_unfold -----*)

Definition entails_emp_unfold_return_wit_1 :=
(
forall (A: Assertion) (PreH1 : (entails_emp A )),
  (A )
|--
  TT && emp 
) \/
(
forall (A: Assertion) (PreH1 : (entails_emp A )),
  (A )
|--
  TT && emp 
).

Definition entails_emp_unfold_return_wit_1_split_goal_spatial :=
forall (A: Assertion) (PreH1 : (entails_emp A )),
  (A )
|--
  TT && emp 
.

(*----- Function ht_specs_get_hash_spec -----*)

Definition ht_specs_get_hash_spec_return_wit_1 :=
(
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
(  TT && emp 
&&
(func_ptr_spec hash_pre (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F)))
) \/
(
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
(  TT && emp 
&&
(func_ptr_spec hash_pre (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F)))
).

(*----- Function ht_specs_get_equal_spec -----*)

Definition ht_specs_get_equal_spec_return_wit_1 :=
(
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
(  TT && emp 
&&
(func_ptr_spec equal_pre (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F)))
) \/
(
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
(  TT && emp 
&&
(func_ptr_spec equal_pre (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F)))
).

(*----- Function ht_specs_get_key_free_spec -----*)

Definition ht_specs_get_key_free_spec_return_wit_1 :=
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
  (“ (key_free_pre = 0) ”
  &&  “ forall (x: Z), forall (k: K), (entails_emp (storeK (x) (k)) ) ”
  &&  emp)
  ||
((  “ (key_free_pre <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  emp
&&
(func_ptr_spec key_free_pre (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))))
.

(*----- Function ht_specs_get_value_free_spec -----*)

Definition ht_specs_get_value_free_spec_return_wit_1 :=
forall (V: Type) (K: Type) (key_eq: (K -> (K -> Prop))) (key_hash: (K -> Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z),
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash_pre equal_pre key_free_pre value_free_pre))
|--
  (“ (value_free_pre = 0) ”
  &&  “ forall (x: Z), forall (v: V), (entails_emp (storeV (x) (v)) ) ”
  &&  emp)
  ||
((  “ (value_free_pre <> 0) ”
  &&  “ (store_exclusive storeV ) ”
  &&  emp
&&
(func_ptr_spec value_free_pre (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))))
.

(*----- Function ht_store_map_unfold -----*)

Definition ht_store_map_unfold_return_wit_1 :=
(
forall (V: Type) (K: Type) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z),
  (ht_store_map storeK storeV key_eq key_hash h_pre m )
|--
  EX (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z),
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
) \/
(
forall (V: Type) (K: Type) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z),
  (ht_store_map storeK storeV key_eq key_hash h_pre m )
|--
  EX (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)),
(  “ (0 < (Zlength (ptrs))) ”
  &&  “ ((Zlength (buckets)) = (Zlength (ptrs))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash (Zlength (ptrs)) buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> (Zlength (ptrs)))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks (Zlength (ptrs)) ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
).

(*----- Function ht_bucket_chains_split_Znth -----*)

Definition ht_bucket_chains_split_Znth_return_wit_1 :=
(
forall (V: Type) (K: Type) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (idx_pre: Z) __default__List__Prod_K_V (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < (Zlength (ptrs)))) (PreH3 : ((Zlength (ptrs)) = (Zlength (buckets)))),
  (ht_bucket_chains storeK storeV ptrs buckets )
|--
  (ht_bucket_chains_except storeK storeV idx_pre ptrs buckets )
  **  (ht_chain storeK storeV (Znth idx_pre ptrs 0) (Znth idx_pre buckets __default__List__Prod_K_V) )
) \/
(
forall (V: Type) (K: Type) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (idx_pre: Z) __default__List__Prod_K_V (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < (Zlength (ptrs)))) (PreH3 : ((Zlength (ptrs)) = (Zlength (buckets)))),
  (ht_bucket_chains storeK storeV ptrs buckets )
|--
  (ht_bucket_chains_except storeK storeV idx_pre ptrs buckets )
  **  (ht_chain storeK storeV (Znth idx_pre ptrs 0) (Znth idx_pre buckets __default__List__Prod_K_V) )
).

Definition ht_bucket_chains_split_Znth_return_wit_1_split_goal_spatial :=
forall (V: Type) (K: Type) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (idx_pre: Z) __default__List__Prod_K_V (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < (Zlength (ptrs)))) (PreH3 : ((Zlength (ptrs)) = (Zlength (buckets)))),
  (ht_bucket_chains storeK storeV ptrs buckets )
|--
  (ht_bucket_chains_except storeK storeV idx_pre ptrs buckets )
  **  (ht_chain storeK storeV (Znth idx_pre ptrs 0) (Znth idx_pre buckets __default__List__Prod_K_V) )
.

(*----- Function ht_chain_nonnull_unfold -----*)

Definition ht_chain_nonnull_unfold_return_wit_1 :=
(
forall (V: Type) (K: Type) (bucket: (@list (K * V))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (node_pre: Z) (PreH1 : (node_pre <> 0)),
  (ht_chain storeK storeV node_pre bucket )
|--
  EX (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))),
  “ (bucket = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  ((&((node_pre)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node_pre)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node_pre)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
) \/
(
forall (V: Type) (K: Type) (bucket: (@list (K * V))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (node_pre: Z) (PreH1 : (node_pre <> 0)),
  (ht_chain storeK storeV node_pre bucket )
|--
  EX (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))),
  “ (bucket = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  ((&((node_pre)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node_pre)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node_pre)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
).

(*----- Function ht_ptr_equal -----*)

Definition ht_ptr_equal_safety_wit_1 :=
forall (lhs_pre: Z) (rhs_pre: Z) (PreH1 : (lhs_pre = rhs_pre)),
  ((( &( "lhs" ) )) # Ptr  |-> lhs_pre)
  **  ((( &( "rhs" ) )) # Ptr  |-> rhs_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_ptr_equal_safety_wit_2 :=
forall (lhs_pre: Z) (rhs_pre: Z) (PreH1 : (lhs_pre <> rhs_pre)),
  ((( &( "lhs" ) )) # Ptr  |-> lhs_pre)
  **  ((( &( "rhs" ) )) # Ptr  |-> rhs_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_ptr_equal_return_wit_1 :=
forall (lhs_pre: Z) (rhs_pre: Z) (PreH1 : (lhs_pre <> rhs_pre)),
  TT && emp 
|--
  “ (lhs_pre <> rhs_pre) ”
  &&  “ (0 = 0) ”
  &&  emp
.

Definition ht_ptr_equal_return_wit_2 :=
forall (lhs_pre: Z) (rhs_pre: Z) (PreH1 : (lhs_pre = rhs_pre)),
  TT && emp 
|--
  “ (lhs_pre = rhs_pre) ”
  &&  “ (1 = 1) ”
  &&  emp
.

(*----- Function ht_int_hash -----*)

Definition ht_int_hash_safety_wit_1 :=
forall (key_pre: Z) (PreH1 : (key_pre <= INT64_MAX)) (PreH2 : (key_pre >= INT64_MIN)),
  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  “ (32 <= 63) ”
  &&  “ (0 <= 32) ”
.

Definition ht_int_hash_safety_wit_2 :=
forall (key_pre: Z) (PreH1 : (key_pre <= INT64_MAX)) (PreH2 : (key_pre >= INT64_MIN)),
  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition ht_int_hash_return_wit_1 :=
(
forall (key_pre: Z) (PreH1 : (key_pre <= INT64_MAX)) (PreH2 : (key_pre >= INT64_MIN)),
  TT && emp 
|--
  “ ((Z.lxor (unsigned_last_nbits (key_pre) (32)) (unsigned_last_nbits ((Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32)) (32))) = (Z.lxor (unsigned_last_nbits (key_pre) (32)) (Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32))) ”
  &&  emp
) \/
(
forall (key_pre: Z) (PreH1 : (key_pre <= INT64_MAX)) (PreH2 : (key_pre >= INT64_MIN)),
  TT && emp 
|--
  “ ((Z.lxor (unsigned_last_nbits (key_pre) (32)) (unsigned_last_nbits ((Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32)) (32))) = (Z.lxor (unsigned_last_nbits (key_pre) (32)) (Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32))) ”
  &&  emp
).

Definition ht_int_hash_return_wit_1_split_goal_1 :=
forall (key_pre: Z) (PreH1 : (key_pre <= INT64_MAX)) (PreH2 : (key_pre >= INT64_MIN)),
  ((Z.lxor (unsigned_last_nbits (key_pre) (32)) (unsigned_last_nbits ((Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32)) (32))) = (Z.lxor (unsigned_last_nbits (key_pre) (32)) (Z.shiftr (unsigned_last_nbits (key_pre) (64)) 32)))
.

(*----- Function ht_init -----*)

Definition ht_init_return_wit_1 :=
(
forall (V: Type) (K: Type) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (capacity_pre: Z) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (h_pre <> 0)) (PreH3 : (0 < capacity_pre)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )),
(  (PtrArray.full retval capacity_pre (zeros (capacity_pre)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
|--
  (ht_store_map storeK storeV key_eq key_hash h_pre empty_mapping )
) \/
(
forall (V: Type) (K: Type) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (capacity_pre: Z) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z) (retval: Z) (PreH1 : (capacity_pre <= UINT_MAX)) (PreH2 : (capacity_pre >= 0)) (PreH3 : (retval <> 0)) (PreH4 : (h_pre <> 0)) (PreH5 : (0 < capacity_pre)) (PreH6 : (key_eq_equiv key_eq )) (PreH7 : (key_eq_hash_compatible key_eq key_hash )),
(  (PtrArray.full retval capacity_pre (zeros (capacity_pre)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
|--
  (ht_store_map storeK storeV key_eq key_hash h_pre empty_mapping )
).

Definition ht_init_return_wit_1_split_goal_spatial :=
forall (V: Type) (K: Type) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (capacity_pre: Z) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z) (retval: Z) (PreH1 : (capacity_pre <= UINT_MAX)) (PreH2 : (capacity_pre >= 0)) (PreH3 : (retval <> 0)) (PreH4 : (h_pre <> 0)) (PreH5 : (0 < capacity_pre)) (PreH6 : (key_eq_equiv key_eq )) (PreH7 : (key_eq_hash_compatible key_eq key_hash )),
(  (PtrArray.full retval capacity_pre (zeros (capacity_pre)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
|--
  (ht_store_map storeK storeV key_eq key_hash h_pre empty_mapping )
.

Definition ht_init_partial_solve_wit_1_pure :=
forall (V: Type) (K: Type) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (capacity_pre: Z) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z) (PreH1 : (h_pre <> 0)) (PreH2 : (0 < capacity_pre)) (PreH3 : (key_eq_equiv key_eq )) (PreH4 : (key_eq_hash_compatible key_eq key_hash )),
(  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "capacity" ) )) # UInt  |-> capacity_pre)
  **  ((( &( "hash" ) )) # Ptr  |-> hash_pre)
  **  ((( &( "equal" ) )) # Ptr  |-> equal_pre)
  **  ((( &( "key_free" ) )) # Ptr  |-> key_free_pre)
  **  ((( &( "value_free" ) )) # Ptr  |-> value_free_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
|--
  “ (0 < capacity_pre) ”
.

Definition ht_init_partial_solve_wit_1_aux :=
forall (V: Type) (K: Type) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (capacity_pre: Z) (hash_pre: Z) (equal_pre: Z) (key_free_pre: Z) (value_free_pre: Z) (PreH1 : (h_pre <> 0)) (PreH2 : (0 < capacity_pre)) (PreH3 : (key_eq_equiv key_eq )) (PreH4 : (key_eq_hash_compatible key_eq key_hash )),
(  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
|--
(  “ (0 < capacity_pre) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (0 < capacity_pre) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> capacity_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash_pre)
&&
((ht_free_spec storeV value_free_pre)
&&
((ht_free_spec storeK key_free_pre)
&&
((ht_equal_spec storeK key_eq equal_pre)
&&
(ht_hash_spec storeK key_hash hash_pre)))))
.

Definition ht_init_partial_solve_wit_1 := ht_init_partial_solve_wit_1_pure -> ht_init_partial_solve_wit_1_aux.

(*----- Function ht_add -----*)

Definition ht_add_safety_wit_1 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (cap <> 0) ”
.

Definition ht_add_safety_wit_2 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (index = ((key_hash (k)) % ( cap ) ))) (PreH2 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH3 : (key_eq_equiv key_eq )) (PreH4 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH5 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH6 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH7 : (retval = (key_hash (k)))) (PreH8 : (0 <= (key_hash (k)))) (PreH9 : ((key_hash (k)) <= UINT_MAX)) (PreH10 : (0 < cap)) (PreH11 : ((Zlength (ptrs)) = cap)) (PreH12 : ((Zlength (buckets)) = cap)) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : (key_eq_hash_compatible key_eq key_hash )) (PreH15 : (buckets_abs key_eq buckets m )) (PreH16 : (buckets_hash key_hash cap buckets )) (PreH17 : (buckets_unique key_eq buckets )) (PreH18 : (h_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_3 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_2 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_add_safety_wit_4 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_2 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_add_safety_wit_5 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_key <> key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq cur_k k )) (PreH5 : (retval_2 = 1)) (PreH6 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (index = ((key_hash (k)) % ( cap ) ))) (PreH9 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH12 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH13 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH14 : (retval = (key_hash (k)))) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : ((key_hash (k)) <= UINT_MAX)) (PreH17 : (0 < cap)) (PreH18 : ((Zlength (ptrs)) = cap)) (PreH19 : ((Zlength (buckets)) = cap)) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : (key_eq_hash_compatible key_eq key_hash )) (PreH22 : (buckets_abs key_eq buckets m )) (PreH23 : (buckets_hash key_hash cap buckets )) (PreH24 : (buckets_unique key_eq buckets )) (PreH25 : (h_pre <> 0)) (PreH26 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_6 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_key <> key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq cur_k k )) (PreH5 : (retval_2 = 1)) (PreH6 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (index = ((key_hash (k)) % ( cap ) ))) (PreH9 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH12 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH13 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH14 : (retval = (key_hash (k)))) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : ((key_hash (k)) <= UINT_MAX)) (PreH17 : (0 < cap)) (PreH18 : ((Zlength (ptrs)) = cap)) (PreH19 : ((Zlength (buckets)) = cap)) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : (key_eq_hash_compatible key_eq key_hash )) (PreH22 : (buckets_abs key_eq buckets m )) (PreH23 : (buckets_hash key_hash cap buckets )) (PreH24 : (buckets_unique key_eq buckets )) (PreH25 : (h_pre <> 0)) (PreH26 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_7 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq cur_k k )) (PreH6 : (retval_2 = 1)) (PreH7 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH11 : (key_eq_equiv key_eq )) (PreH12 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH13 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH14 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH15 : (retval = (key_hash (k)))) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : ((key_hash (k)) <= UINT_MAX)) (PreH18 : (0 < cap)) (PreH19 : ((Zlength (ptrs)) = cap)) (PreH20 : ((Zlength (buckets)) = cap)) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : (key_eq_hash_compatible key_eq key_hash )) (PreH23 : (buckets_abs key_eq buckets m )) (PreH24 : (buckets_hash key_hash cap buckets )) (PreH25 : (buckets_unique key_eq buckets )) (PreH26 : (h_pre <> 0)) (PreH27 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ False ”
.

Definition ht_add_safety_wit_8 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq cur_k k )) (PreH6 : (retval_2 = 1)) (PreH7 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH11 : (key_eq_equiv key_eq )) (PreH12 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH13 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH14 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH15 : (retval = (key_hash (k)))) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : ((key_hash (k)) <= UINT_MAX)) (PreH18 : (0 < cap)) (PreH19 : ((Zlength (ptrs)) = cap)) (PreH20 : ((Zlength (buckets)) = cap)) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : (key_eq_hash_compatible key_eq key_hash )) (PreH23 : (buckets_abs key_eq buckets m )) (PreH24 : (buckets_hash key_hash cap buckets )) (PreH25 : (buckets_unique key_eq buckets )) (PreH26 : (h_pre <> 0)) (PreH27 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_add_safety_wit_9 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (key_free = 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_10 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH4 : (key_free = 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_11 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free <> 0)) (PreH6 : (store_exclusive storeK )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_12 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free <> 0)) (PreH6 : (store_exclusive storeK )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_13 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free = 0)) (PreH6 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_14 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free = 0)) (PreH6 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_15 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (key_free <> 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_16 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val <> val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH4 : (key_free <> 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_add_safety_wit_17 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free = 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ False ”
.

Definition ht_add_safety_wit_18 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH5 : (key_free = 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_add_safety_wit_19 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  “ False ”
.

Definition ht_add_safety_wit_20 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ False ”
.

Definition ht_add_safety_wit_21 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ False ”
.

Definition ht_add_safety_wit_22 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_add_safety_wit_23 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free <> 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  “ False ”
.

Definition ht_add_safety_wit_24 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH5 : (key_free <> 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  “ False ”
.

Definition ht_add_entail_wit_1 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |-> (retval % ( cap ) ))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)),
(  TT && emp 
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ ((retval % ( cap ) ) < cap) ”
  &&  “ (0 <= (retval % ( cap ) )) ”
  &&  emp
).

Definition ht_add_entail_wit_1_split_goal_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)),
  ((retval % ( cap ) ) < cap)
.

Definition ht_add_entail_wit_1_split_goal_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)),
  (0 <= (retval % ( cap ) ))
.

Definition ht_add_entail_wit_2 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
(  (PtrArray.full bucks cap ptrs )
  **  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) l1 )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
(  TT && emp 
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) (@nil (K * V)) ) -> ~((key_eq pk k ))) ”
  &&  “ ((app ((@nil (K * V))) ((Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))) = (Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V)) ”
  &&  emp
).

Definition ht_add_entail_wit_2_split_goal_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
  forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) (@nil (K * V)) ) -> ~((key_eq pk k )))
.

Definition ht_add_entail_wit_2_split_goal_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
  ((app ((@nil (K * V))) ((Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))) = (Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))
.

Definition ht_add_entail_wit_3_1 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_5: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_5 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_5 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (retval_2: Z),
(  “ ~((key_eq cur_k k )) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_entail_wit_3_2 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_2 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_2 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ ~((key_eq cur_k k )) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_entail_wit_4_1 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_entail_wit_4_2 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_5: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_5 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_5 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (retval_2: Z),
(  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_entail_wit_5 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1_2: (@list (K * V))) (l2_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_3 = 0)) (PreH3 : (l2_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1_2) (l2_2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1_2 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_3 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1_2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_4 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_4 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_4 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth index ptrs 0) cur_next l1 )
  **  (ht_chain storeK storeV cur_next l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1_2: (@list (K * V))) (l2_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_3 = 0)) (PreH3 : (l2_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1_2) (l2_2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1_2 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_3 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1_2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_4 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_4 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_4 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth index ptrs 0) cur_next l1 )
  **  (ht_chain storeK storeV cur_next l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (storeK key_pre k )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
).

Definition ht_add_return_wit_1 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free = 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free <> 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free <> 0)) (PreH6 : (store_exclusive storeV )) (PreH7 : (key_free = 0)) (PreH8 : (cur_key <> key_pre)) (PreH9 : (key_free = 0)) (PreH10 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH11 : (key_eq cur_k k )) (PreH12 : (retval_2 = 1)) (PreH13 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH14 : (node <> 0)) (PreH15 : (index = ((key_hash (k)) % ( cap ) ))) (PreH16 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH19 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH20 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH21 : (retval = (key_hash (k)))) (PreH22 : (0 <= (key_hash (k)))) (PreH23 : ((key_hash (k)) <= UINT_MAX)) (PreH24 : (0 < cap)) (PreH25 : ((Zlength (ptrs)) = cap)) (PreH26 : ((Zlength (buckets)) = cap)) (PreH27 : (key_eq_equiv key_eq )) (PreH28 : (key_eq_hash_compatible key_eq key_hash )) (PreH29 : (buckets_abs key_eq buckets m )) (PreH30 : (buckets_hash key_hash cap buckets )) (PreH31 : (buckets_unique key_eq buckets )) (PreH32 : (h_pre <> 0)) (PreH33 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_2 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free <> 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free <> 0)) (PreH6 : (store_exclusive storeV )) (PreH7 : (cur_key = key_pre)) (PreH8 : (key_free <> 0)) (PreH9 : (store_exclusive storeK )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_3 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free <> 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free <> 0)) (PreH6 : (store_exclusive storeV )) (PreH7 : (cur_key = key_pre)) (PreH8 : (key_free = 0)) (PreH9 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_4 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free <> 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free <> 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free <> 0)) (PreH6 : (store_exclusive storeV )) (PreH7 : (key_free <> 0)) (PreH8 : (cur_key <> key_pre)) (PreH9 : (key_free <> 0)) (PreH10 : (store_exclusive storeK )) (PreH11 : (key_eq cur_k k )) (PreH12 : (retval_2 = 1)) (PreH13 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH14 : (node <> 0)) (PreH15 : (index = ((key_hash (k)) % ( cap ) ))) (PreH16 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH19 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH20 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH21 : (retval = (key_hash (k)))) (PreH22 : (0 <= (key_hash (k)))) (PreH23 : ((key_hash (k)) <= UINT_MAX)) (PreH24 : (0 < cap)) (PreH25 : ((Zlength (ptrs)) = cap)) (PreH26 : ((Zlength (buckets)) = cap)) (PreH27 : (key_eq_equiv key_eq )) (PreH28 : (key_eq_hash_compatible key_eq key_hash )) (PreH29 : (buckets_abs key_eq buckets m )) (PreH30 : (buckets_hash key_hash cap buckets )) (PreH31 : (buckets_unique key_eq buckets )) (PreH32 : (h_pre <> 0)) (PreH33 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_5 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH4 : (key_free <> 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free = 0)) (PreH5 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH6 : (key_free <> 0)) (PreH7 : (cur_key <> key_pre)) (PreH8 : (key_free <> 0)) (PreH9 : (store_exclusive storeK )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_6 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (key_free <> 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free <> 0)) (PreH5 : (store_exclusive storeV )) (PreH6 : (key_free <> 0)) (PreH7 : (cur_key <> key_pre)) (PreH8 : (key_free <> 0)) (PreH9 : (store_exclusive storeK )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_7 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free = 0)) (PreH6 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free = 0)) (PreH5 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH6 : (cur_key = key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_8 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free = 0)) (PreH6 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free <> 0)) (PreH5 : (store_exclusive storeV )) (PreH6 : (cur_key = key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_9 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free <> 0)) (PreH6 : (store_exclusive storeK )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free = 0)) (PreH5 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH6 : (cur_key = key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_10 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (cur_key = key_pre)) (PreH5 : (key_free <> 0)) (PreH6 : (store_exclusive storeK )) (PreH7 : (key_eq cur_k k )) (PreH8 : (retval_2 = 1)) (PreH9 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH10 : (node <> 0)) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH15 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH16 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH17 : (retval = (key_hash (k)))) (PreH18 : (0 <= (key_hash (k)))) (PreH19 : ((key_hash (k)) <= UINT_MAX)) (PreH20 : (0 < cap)) (PreH21 : ((Zlength (ptrs)) = cap)) (PreH22 : ((Zlength (buckets)) = cap)) (PreH23 : (key_eq_equiv key_eq )) (PreH24 : (key_eq_hash_compatible key_eq key_hash )) (PreH25 : (buckets_abs key_eq buckets m )) (PreH26 : (buckets_hash key_hash cap buckets )) (PreH27 : (buckets_unique key_eq buckets )) (PreH28 : (h_pre <> 0)) (PreH29 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free <> 0)) (PreH5 : (store_exclusive storeV )) (PreH6 : (cur_key = key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_11 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free = 0)) (PreH3 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH4 : (key_free = 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free = 0)) (PreH5 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH6 : (key_free = 0)) (PreH7 : (cur_key <> key_pre)) (PreH8 : (key_free = 0)) (PreH9 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_12 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_val = val_pre)) (PreH2 : (value_free <> 0)) (PreH3 : (store_exclusive storeV )) (PreH4 : (key_free = 0)) (PreH5 : (cur_key <> key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (cur_val = val_pre)) (PreH4 : (value_free <> 0)) (PreH5 : (store_exclusive storeV )) (PreH6 : (key_free = 0)) (PreH7 : (cur_key <> key_pre)) (PreH8 : (key_free = 0)) (PreH9 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_13 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH5 : (key_free <> 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free = 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free = 0)) (PreH6 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH7 : (key_free <> 0)) (PreH8 : (cur_key <> key_pre)) (PreH9 : (key_free <> 0)) (PreH10 : (store_exclusive storeK )) (PreH11 : (key_eq cur_k k )) (PreH12 : (retval_2 = 1)) (PreH13 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH14 : (node <> 0)) (PreH15 : (index = ((key_hash (k)) % ( cap ) ))) (PreH16 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH19 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH20 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH21 : (retval = (key_hash (k)))) (PreH22 : (0 <= (key_hash (k)))) (PreH23 : ((key_hash (k)) <= UINT_MAX)) (PreH24 : (0 < cap)) (PreH25 : ((Zlength (ptrs)) = cap)) (PreH26 : ((Zlength (buckets)) = cap)) (PreH27 : (key_eq_equiv key_eq )) (PreH28 : (key_eq_hash_compatible key_eq key_hash )) (PreH29 : (buckets_abs key_eq buckets m )) (PreH30 : (buckets_hash key_hash cap buckets )) (PreH31 : (buckets_unique key_eq buckets )) (PreH32 : (h_pre <> 0)) (PreH33 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_14 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free = 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free = 0)) (PreH6 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH7 : (cur_key = key_pre)) (PreH8 : (key_free = 0)) (PreH9 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_15 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free = 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free = 0)) (PreH6 : forall (x: Z), forall (v_2: V), (entails_emp (storeV (x) (v_2)) )) (PreH7 : (cur_key = key_pre)) (PreH8 : (key_free <> 0)) (PreH9 : (store_exclusive storeK )) (PreH10 : (key_eq cur_k k )) (PreH11 : (retval_2 = 1)) (PreH12 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH13 : (node <> 0)) (PreH14 : (index = ((key_hash (k)) % ( cap ) ))) (PreH15 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH16 : (key_eq_equiv key_eq )) (PreH17 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH18 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH19 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH20 : (retval = (key_hash (k)))) (PreH21 : (0 <= (key_hash (k)))) (PreH22 : ((key_hash (k)) <= UINT_MAX)) (PreH23 : (0 < cap)) (PreH24 : ((Zlength (ptrs)) = cap)) (PreH25 : ((Zlength (buckets)) = cap)) (PreH26 : (key_eq_equiv key_eq )) (PreH27 : (key_eq_hash_compatible key_eq key_hash )) (PreH28 : (buckets_abs key_eq buckets m )) (PreH29 : (buckets_hash key_hash cap buckets )) (PreH30 : (buckets_unique key_eq buckets )) (PreH31 : (h_pre <> 0)) (PreH32 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_16 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free = 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free = 0)) (PreH4 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH5 : (key_free = 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (value_free = 0)) (PreH4 : (cur_val <> val_pre)) (PreH5 : (value_free = 0)) (PreH6 : forall (x_2: Z), forall (v_2: V), (entails_emp (storeV (x_2) (v_2)) )) (PreH7 : (key_free = 0)) (PreH8 : (cur_key <> key_pre)) (PreH9 : (key_free = 0)) (PreH10 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH11 : (key_eq cur_k k )) (PreH12 : (retval_2 = 1)) (PreH13 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH14 : (node <> 0)) (PreH15 : (index = ((key_hash (k)) % ( cap ) ))) (PreH16 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH19 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH20 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH21 : (retval = (key_hash (k)))) (PreH22 : (0 <= (key_hash (k)))) (PreH23 : ((key_hash (k)) <= UINT_MAX)) (PreH24 : (0 < cap)) (PreH25 : ((Zlength (ptrs)) = cap)) (PreH26 : ((Zlength (buckets)) = cap)) (PreH27 : (key_eq_equiv key_eq )) (PreH28 : (key_eq_hash_compatible key_eq key_hash )) (PreH29 : (buckets_abs key_eq buckets m )) (PreH30 : (buckets_hash key_hash cap buckets )) (PreH31 : (buckets_unique key_eq buckets )) (PreH32 : (h_pre <> 0)) (PreH33 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_return_wit_17 :=
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (retval_2 <> 0)) (PreH2 : (node = 0)) (PreH3 : (index = ((key_hash (k)) % ( cap ) ))) (PreH4 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH5 : (key_eq_equiv key_eq )) (PreH6 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH7 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH8 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH9 : (retval = (key_hash (k)))) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : ((key_hash (k)) <= UINT_MAX)) (PreH12 : (0 < cap)) (PreH13 : ((Zlength (ptrs)) = cap)) (PreH14 : ((Zlength (buckets)) = cap)) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : (key_eq_hash_compatible key_eq key_hash )) (PreH17 : (buckets_abs key_eq buckets m )) (PreH18 : (buckets_hash key_hash cap buckets )) (PreH19 : (buckets_unique key_eq buckets )) (PreH20 : (h_pre <> 0)),
(  (PtrArray.full bucks cap (replace_Znth (index) (retval_2) (ptrs)) )
  **  ((&((retval_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> (Znth index ptrs 0))
  **  ((&((retval_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((retval_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
) \/
(
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cap <= UINT_MAX)) (PreH2 : (cap >= 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (node = 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)),
(  (PtrArray.full bucks cap (replace_Znth (index) (retval_2) (ptrs)) )
  **  ((&((retval_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> (Znth index ptrs 0))
  **  ((&((retval_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((retval_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (new_m: (@mapping K V)),
  “ (map_insert key_eq k v m new_m ) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre new_m )
).

Definition ht_add_partial_solve_wit_1 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (PreH1 : (h_pre <> 0)),
  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  (storeV val_pre v )
|--
  “ (h_pre <> 0) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  (storeV val_pre v )
.

Definition ht_add_partial_solve_wit_2 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeK key_pre k )
  **  (storeV val_pre v )
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_3 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeK key_pre k )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_4_pure :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
.

Definition ht_add_partial_solve_wit_4_aux :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_4 := ht_add_partial_solve_wit_4_pure -> ht_add_partial_solve_wit_4_aux.

Definition ht_add_partial_solve_wit_5 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
(  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_6 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (((bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((key_hash (k)) % ( cap ) ) ptrs 0))
  **  (PtrArray.missing_i bucks ((key_hash (k)) % ( cap ) ) 0 cap ptrs )
  **  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_7 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_8_pure :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (node <> 0) ”
.

Definition ht_add_partial_solve_wit_8_aux :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (node <> 0) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain storeK storeV node l2 )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_partial_solve_wit_8 := ht_add_partial_solve_wit_8_pure -> ht_add_partial_solve_wit_8_aux.

Definition ht_add_partial_solve_wit_9 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) __default__List__Prod_K_V (PreH1 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH2 : (node <> 0)) (PreH3 : (index = ((key_hash (k)) % ( cap ) ))) (PreH4 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH5 : (key_eq_equiv key_eq )) (PreH6 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH7 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH8 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH9 : (retval = (key_hash (k)))) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : ((key_hash (k)) <= UINT_MAX)) (PreH12 : (0 < cap)) (PreH13 : ((Zlength (ptrs)) = cap)) (PreH14 : ((Zlength (buckets)) = cap)) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : (key_eq_hash_compatible key_eq key_hash )) (PreH17 : (buckets_abs key_eq buckets m )) (PreH18 : (buckets_hash key_hash cap buckets )) (PreH19 : (buckets_unique key_eq buckets )) (PreH20 : (h_pre <> 0)),
(  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_add_partial_solve_wit_10 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_11 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq cur_k k )) (PreH6 : (retval_2 = 1)) (PreH7 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH11 : (key_eq_equiv key_eq )) (PreH12 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH13 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH14 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH15 : (retval = (key_hash (k)))) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : ((key_hash (k)) <= UINT_MAX)) (PreH18 : (0 < cap)) (PreH19 : ((Zlength (ptrs)) = cap)) (PreH20 : ((Zlength (buckets)) = cap)) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : (key_eq_hash_compatible key_eq key_hash )) (PreH23 : (buckets_abs key_eq buckets m )) (PreH24 : (buckets_hash key_hash cap buckets )) (PreH25 : (buckets_unique key_eq buckets )) (PreH26 : (h_pre <> 0)) (PreH27 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
(  “ (key_free <> 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
.

Definition ht_add_partial_solve_wit_12 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq cur_k k )) (PreH6 : (retval_2 = 1)) (PreH7 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH11 : (key_eq_equiv key_eq )) (PreH12 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH13 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH14 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH15 : (retval = (key_hash (k)))) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : ((key_hash (k)) <= UINT_MAX)) (PreH18 : (0 < cap)) (PreH19 : ((Zlength (ptrs)) = cap)) (PreH20 : ((Zlength (buckets)) = cap)) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : (key_eq_hash_compatible key_eq key_hash )) (PreH23 : (buckets_abs key_eq buckets m )) (PreH24 : (buckets_hash key_hash cap buckets )) (PreH25 : (buckets_unique key_eq buckets )) (PreH26 : (h_pre <> 0)) (PreH27 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_13 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq cur_k k )) (PreH5 : (retval_2 = 1)) (PreH6 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (index = ((key_hash (k)) % ( cap ) ))) (PreH9 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH12 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH13 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH14 : (retval = (key_hash (k)))) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : ((key_hash (k)) <= UINT_MAX)) (PreH17 : (0 < cap)) (PreH18 : ((Zlength (ptrs)) = cap)) (PreH19 : ((Zlength (buckets)) = cap)) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : (key_eq_hash_compatible key_eq key_hash )) (PreH22 : (buckets_abs key_eq buckets m )) (PreH23 : (buckets_hash key_hash cap buckets )) (PreH24 : (buckets_unique key_eq buckets )) (PreH25 : (h_pre <> 0)) (PreH26 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_14 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq cur_k k )) (PreH5 : (retval_2 = 1)) (PreH6 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (index = ((key_hash (k)) % ( cap ) ))) (PreH9 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH12 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH13 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH14 : (retval = (key_hash (k)))) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : ((key_hash (k)) <= UINT_MAX)) (PreH17 : (0 < cap)) (PreH18 : ((Zlength (ptrs)) = cap)) (PreH19 : ((Zlength (buckets)) = cap)) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : (key_eq_hash_compatible key_eq key_hash )) (PreH22 : (buckets_abs key_eq buckets m )) (PreH23 : (buckets_hash key_hash cap buckets )) (PreH24 : (buckets_unique key_eq buckets )) (PreH25 : (h_pre <> 0)) (PreH26 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_15 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq cur_k k )) (PreH6 : (retval_2 = 1)) (PreH7 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH11 : (key_eq_equiv key_eq )) (PreH12 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH13 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH14 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH15 : (retval = (key_hash (k)))) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : ((key_hash (k)) <= UINT_MAX)) (PreH18 : (0 < cap)) (PreH19 : ((Zlength (ptrs)) = cap)) (PreH20 : ((Zlength (buckets)) = cap)) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : (key_eq_hash_compatible key_eq key_hash )) (PreH23 : (buckets_abs key_eq buckets m )) (PreH24 : (buckets_hash key_hash cap buckets )) (PreH25 : (buckets_unique key_eq buckets )) (PreH26 : (h_pre <> 0)) (PreH27 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # Ptr  |-> val_pre)
  **  (storeV val_pre v )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_add_partial_solve_wit_16 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free = 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free = 0)) (PreH8 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
(  “ (value_free <> 0) ”
  &&  “ (cur_val <> val_pre) ”
  &&  “ (value_free <> 0) ”
  &&  “ (store_exclusive storeV ) ”
  &&  “ (key_free = 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free = 0) ”
  &&  “ forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) ) ”
  &&  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeV cur_val cur_v )
  **  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
.

Definition ht_add_partial_solve_wit_17 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free <> 0)) (PreH7 : (store_exclusive storeK )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
(  “ (value_free <> 0) ”
  &&  “ (cur_val <> val_pre) ”
  &&  “ (value_free <> 0) ”
  &&  “ (store_exclusive storeV ) ”
  &&  “ (cur_key = key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeV cur_val cur_v )
  **  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
.

Definition ht_add_partial_solve_wit_18 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (cur_key = key_pre)) (PreH6 : (key_free = 0)) (PreH7 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH8 : (key_eq cur_k k )) (PreH9 : (retval_2 = 1)) (PreH10 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH11 : (node <> 0)) (PreH12 : (index = ((key_hash (k)) % ( cap ) ))) (PreH13 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH16 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH17 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH18 : (retval = (key_hash (k)))) (PreH19 : (0 <= (key_hash (k)))) (PreH20 : ((key_hash (k)) <= UINT_MAX)) (PreH21 : (0 < cap)) (PreH22 : ((Zlength (ptrs)) = cap)) (PreH23 : ((Zlength (buckets)) = cap)) (PreH24 : (key_eq_equiv key_eq )) (PreH25 : (key_eq_hash_compatible key_eq key_hash )) (PreH26 : (buckets_abs key_eq buckets m )) (PreH27 : (buckets_hash key_hash cap buckets )) (PreH28 : (buckets_unique key_eq buckets )) (PreH29 : (h_pre <> 0)) (PreH30 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
|--
(  “ (value_free <> 0) ”
  &&  “ (cur_val <> val_pre) ”
  &&  “ (value_free <> 0) ”
  &&  “ (store_exclusive storeV ) ”
  &&  “ (cur_key = key_pre) ”
  &&  “ (key_free = 0) ”
  &&  “ forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) ) ”
  &&  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeV cur_val cur_v )
  **  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 key_k )))
  (fun arg_pre_2 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_2 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))))
.

Definition ht_add_partial_solve_wit_19 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (value_free <> 0)) (PreH2 : (cur_val <> val_pre)) (PreH3 : (value_free <> 0)) (PreH4 : (store_exclusive storeV )) (PreH5 : (key_free <> 0)) (PreH6 : (cur_key <> key_pre)) (PreH7 : (key_free <> 0)) (PreH8 : (store_exclusive storeK )) (PreH9 : (key_eq cur_k k )) (PreH10 : (retval_2 = 1)) (PreH11 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH12 : (node <> 0)) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH17 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH18 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH19 : (retval = (key_hash (k)))) (PreH20 : (0 <= (key_hash (k)))) (PreH21 : ((key_hash (k)) <= UINT_MAX)) (PreH22 : (0 < cap)) (PreH23 : ((Zlength (ptrs)) = cap)) (PreH24 : ((Zlength (buckets)) = cap)) (PreH25 : (key_eq_equiv key_eq )) (PreH26 : (key_eq_hash_compatible key_eq key_hash )) (PreH27 : (buckets_abs key_eq buckets m )) (PreH28 : (buckets_hash key_hash cap buckets )) (PreH29 : (buckets_unique key_eq buckets )) (PreH30 : (h_pre <> 0)) (PreH31 : (retval_2 <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
|--
(  “ (value_free <> 0) ”
  &&  “ (cur_val <> val_pre) ”
  &&  “ (value_free <> 0) ”
  &&  “ (store_exclusive storeV ) ”
  &&  “ (key_free <> 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeV cur_val cur_v )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec value_free (fun F =>
ALL (v_2: V),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeV arg_pre v_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre_2 =>
  ((storeK arg_pre_2 k_2 )))
  (fun arg_pre_2 (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre_3 =>
  ((storeK arg_pre_3 key_k )))
  (fun arg_pre_3 retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre_3 key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))))
.

Definition ht_add_partial_solve_wit_20 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node = 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (node = 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_21 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (retval_2 <> 0)) (PreH2 : (node = 0)) (PreH3 : (index = ((key_hash (k)) % ( cap ) ))) (PreH4 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH5 : (key_eq_equiv key_eq )) (PreH6 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH7 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH8 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH9 : (retval = (key_hash (k)))) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : ((key_hash (k)) <= UINT_MAX)) (PreH12 : (0 < cap)) (PreH13 : ((Zlength (ptrs)) = cap)) (PreH14 : ((Zlength (buckets)) = cap)) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : (key_eq_hash_compatible key_eq key_hash )) (PreH17 : (buckets_abs key_eq buckets m )) (PreH18 : (buckets_hash key_hash cap buckets )) (PreH19 : (buckets_unique key_eq buckets )) (PreH20 : (h_pre <> 0)),
(  (UndefStructPredht_node retval_2 )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (retval_2 <> 0) ”
  &&  “ (node = 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (((bucks + (index * sizeof(PTR)))) # Ptr  |-> (Znth index ptrs 0))
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  (UndefStructPredht_node retval_2 )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_partial_solve_wit_22 :=
forall (V: Type) (K: Type) (v: V) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (val_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (retval_2 <> 0)) (PreH2 : (node = 0)) (PreH3 : (index = ((key_hash (k)) % ( cap ) ))) (PreH4 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH5 : (key_eq_equiv key_eq )) (PreH6 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k )))) (PreH7 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH8 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH9 : (retval = (key_hash (k)))) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : ((key_hash (k)) <= UINT_MAX)) (PreH12 : (0 < cap)) (PreH13 : ((Zlength (ptrs)) = cap)) (PreH14 : ((Zlength (buckets)) = cap)) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : (key_eq_hash_compatible key_eq key_hash )) (PreH17 : (buckets_abs key_eq buckets m )) (PreH18 : (buckets_hash key_hash cap buckets )) (PreH19 : (buckets_unique key_eq buckets )) (PreH20 : (h_pre <> 0)),
(  ((&((retval_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> (Znth index ptrs 0))
  **  ((&((retval_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((retval_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (retval_2 <> 0) ”
  &&  “ (node = 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq pk k ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  (((bucks + (index * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((&((retval_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> (Znth index ptrs 0))
  **  ((&((retval_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> val_pre)
  **  ((&((retval_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> key_pre)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (storeV val_pre v )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_add_which_implies_wit_1 :=
(
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
) \/
(
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
).

Definition ht_add_which_implies_wit_1_split_goal_spatial :=
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
.

(*----- Function ht_find -----*)

Definition ht_find_safety_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (valid_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (cap <> 0) ”
.

Definition ht_find_safety_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (index = ((key_hash (k)) % ( cap ) ))) (PreH2 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH3 : (key_eq_equiv key_eq )) (PreH4 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH5 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH6 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH7 : (retval = (key_hash (k)))) (PreH8 : (0 <= (key_hash (k)))) (PreH9 : ((key_hash (k)) <= UINT_MAX)) (PreH10 : (0 < cap)) (PreH11 : ((Zlength (ptrs)) = cap)) (PreH12 : ((Zlength (buckets)) = cap)) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : (key_eq_hash_compatible key_eq key_hash )) (PreH15 : (buckets_abs key_eq buckets m )) (PreH16 : (buckets_hash key_hash cap buckets )) (PreH17 : (buckets_unique key_eq buckets )) (PreH18 : (h_pre <> 0)) (PreH19 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_find_safety_wit_3 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_find_safety_wit_4 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_2 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_find_safety_wit_5 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_find_safety_wit_6 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node = 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_find_safety_wit_7 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node = 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |-> 0)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_find_entail_wit_1 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (valid_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |-> (retval % ( cap ) ))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (valid_pre <> 0)),
(  TT && emp 
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ ((retval % ( cap ) ) < cap) ”
  &&  “ (0 <= (retval % ( cap ) )) ”
  &&  emp
).

Definition ht_find_entail_wit_1_split_goal_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (valid_pre <> 0)),
  ((retval % ( cap ) ) < cap)
.

Definition ht_find_entail_wit_1_split_goal_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (valid_pre <> 0)),
  (0 <= (retval % ( cap ) ))
.

Definition ht_find_entail_wit_2 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
(  (PtrArray.full bucks cap ptrs )
  **  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) l1 )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
(  TT && emp 
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) (@nil (K * V)) ) -> ~((key_eq k pk ))) ”
  &&  “ ((app ((@nil (K * V))) ((Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))) = (Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V)) ”
  &&  emp
).

Definition ht_find_entail_wit_2_split_goal_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
  forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) (@nil (K * V)) ) -> ~((key_eq k pk )))
.

Definition ht_find_entail_wit_2_split_goal_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
  ((app ((@nil (K * V))) ((Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))) = (Znth (retval % ( cap ) ) buckets __default__List__Prod_K_V))
.

Definition ht_find_entail_wit_3_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_5: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_5 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_5 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (retval_2: Z),
(  “ ~((key_eq cur_k k )) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_entail_wit_3_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_2 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ ~((key_eq cur_k k )) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_entail_wit_4_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_entail_wit_4_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_5: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_5 = 0)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_5 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (retval_2: Z),
(  “ (key_eq cur_k k ) ”
  &&  “ (retval_2 = 1) ”
  &&  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_entail_wit_5 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1_2: (@list (K * V))) (l2_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_3 = 0)) (PreH3 : (l2_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1_2) (l2_2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1_2 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_3 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1_2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_4 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_4 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_4 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth index ptrs 0) cur_next l1 )
  **  (ht_chain storeK storeV cur_next l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1_2: (@list (K * V))) (l2_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) __default__List__Prod_K_V (PreH1 : ~((key_eq cur_k k ))) (PreH2 : (retval_3 = 0)) (PreH3 : (l2_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1_2) (l2_2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1_2 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_3 = 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1_2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_4 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_4 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_4 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  EX (l1: (@list (K * V))) (l2: (@list (K * V))),
(  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_chain_seg storeK storeV (Znth index ptrs 0) cur_next l1 )
  **  (ht_chain storeK storeV cur_next l2 )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (storeK key_pre k )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
).

Definition ht_find_return_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node = 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |-> 0)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  (EX (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  (storeV 0 v )
  **  ((valid_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map_value_hole storeK storeV key_eq key_hash h_pre m k 0 ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (0 = 0) ”
  &&  ((valid_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_find_return_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_2: Z) __default__List__Prod_K_V (PreH1 : (key_eq cur_k k )) (PreH2 : (retval_2 = 1)) (PreH3 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (index = ((key_hash (k)) % ( cap ) ))) (PreH6 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH9 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH10 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH11 : (retval = (key_hash (k)))) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : ((key_hash (k)) <= UINT_MAX)) (PreH14 : (0 < cap)) (PreH15 : ((Zlength (ptrs)) = cap)) (PreH16 : ((Zlength (buckets)) = cap)) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : (key_eq_hash_compatible key_eq key_hash )) (PreH19 : (buckets_abs key_eq buckets m )) (PreH20 : (buckets_hash key_hash cap buckets )) (PreH21 : (buckets_unique key_eq buckets )) (PreH22 : (h_pre <> 0)) (PreH23 : (valid_pre <> 0)) (PreH24 : (retval_2 <> 0)),
(  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |-> 1)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_3 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_3 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_3 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_4 =>
  (“ (retval_4 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  (EX (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  (storeV cur_val v )
  **  ((valid_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map_value_hole storeK storeV key_eq key_hash h_pre m k cur_val ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (cur_val = 0) ”
  &&  ((valid_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_find_partial_solve_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (PreH1 : (h_pre <> 0)) (PreH2 : (valid_pre <> 0)),
  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  ((valid_pre) # Int  |->_)
.

Definition ht_find_partial_solve_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)) (PreH10 : (valid_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  (storeK key_pre k )
  **  ((valid_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_find_partial_solve_wit_3 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)) (PreH10 : (valid_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeK key_pre k )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_find_partial_solve_wit_4_pure :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)) (PreH16 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
.

Definition ht_find_partial_solve_wit_4_aux :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)) (PreH16 : (valid_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_find_partial_solve_wit_4 := ht_find_partial_solve_wit_4_pure -> ht_find_partial_solve_wit_4_aux.

Definition ht_find_partial_solve_wit_5 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
(  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_find_partial_solve_wit_6 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (valid_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (((bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((key_hash (k)) % ( cap ) ) ptrs 0))
  **  (PtrArray.missing_i bucks ((key_hash (k)) % ( cap ) ) 0 cap ptrs )
  **  (ht_chain_seg storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_find_partial_solve_wit_7 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_find_partial_solve_wit_8_pure :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> index)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (node <> 0) ”
.

Definition ht_find_partial_solve_wit_8_aux :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) __default__List__Prod_K_V (PreH1 : (node <> 0)) (PreH2 : (index = ((key_hash (k)) % ( cap ) ))) (PreH3 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH6 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH7 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH8 : (retval = (key_hash (k)))) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : ((key_hash (k)) <= UINT_MAX)) (PreH11 : (0 < cap)) (PreH12 : ((Zlength (ptrs)) = cap)) (PreH13 : ((Zlength (buckets)) = cap)) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : (key_eq_hash_compatible key_eq key_hash )) (PreH16 : (buckets_abs key_eq buckets m )) (PreH17 : (buckets_hash key_hash cap buckets )) (PreH18 : (buckets_unique key_eq buckets )) (PreH19 : (h_pre <> 0)) (PreH20 : (valid_pre <> 0)),
(  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (ht_chain storeK storeV node l2 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (node <> 0) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (ht_chain storeK storeV node l2 )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_partial_solve_wit_8 := ht_find_partial_solve_wit_8_pure -> ht_find_partial_solve_wit_8_aux.

Definition ht_find_partial_solve_wit_9 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (valid_pre: Z) (bucks: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (cap: Z) (retval: Z) (node: Z) (l1: (@list (K * V))) (l2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) __default__List__Prod_K_V (PreH1 : (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH2 : (node <> 0)) (PreH3 : (index = ((key_hash (k)) % ( cap ) ))) (PreH4 : ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V))) (PreH5 : (key_eq_equiv key_eq )) (PreH6 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk )))) (PreH7 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH8 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH9 : (retval = (key_hash (k)))) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : ((key_hash (k)) <= UINT_MAX)) (PreH12 : (0 < cap)) (PreH13 : ((Zlength (ptrs)) = cap)) (PreH14 : ((Zlength (buckets)) = cap)) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : (key_eq_hash_compatible key_eq key_hash )) (PreH17 : (buckets_abs key_eq buckets m )) (PreH18 : (buckets_hash key_hash cap buckets )) (PreH19 : (buckets_unique key_eq buckets )) (PreH20 : (h_pre <> 0)) (PreH21 : (valid_pre <> 0)),
(  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (l2 = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ ((app (l1) (l2)) = (Znth index buckets __default__List__Prod_K_V)) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) l1 ) -> ~((key_eq k pk ))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (valid_pre <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  (ht_chain_seg storeK storeV (Znth index ptrs 0) node l1 )
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  ((valid_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_3 =>
  (“ (retval_3 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_find_which_implies_wit_1 :=
(
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
) \/
(
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
).

Definition ht_find_which_implies_wit_1_split_goal_spatial :=
forall (V: Type) (K: Type) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (buckets: (@list (@list (K * V)))) (ptrs: (@list Z)) (index: Z) __default__List__Prod_K_V,
  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
|--
  (ht_chain_seg storeK storeV (Znth index ptrs 0) (Znth index ptrs 0) (@nil (K * V)) )
  **  (ht_chain storeK storeV (Znth index ptrs 0) (Znth index buckets __default__List__Prod_K_V) )
.

(*----- Function ht_remove -----*)

Definition ht_remove_safety_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (removed_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |->_)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (cap <> 0) ”
.

Definition ht_remove_safety_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_hash_compatible key_eq key_hash )) (PreH5 : (buckets_abs key_eq buckets m )) (PreH6 : (buckets_hash key_hash cap buckets )) (PreH7 : (buckets_unique key_eq buckets )) (PreH8 : (0 <= (key_hash (k)))) (PreH9 : (index = ((key_hash (k)) % ( cap ) ))) (PreH10 : (0 <= index)) (PreH11 : (index < cap)) (PreH12 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH13 : (key_eq_equiv key_eq )) (PreH14 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_remove_safety_wit_3 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_eq k cur_k )) (PreH2 : (retval = 1)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval = 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ False ”
.

Definition ht_remove_safety_wit_4 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : ~((key_eq k cur_k ))) (PreH2 : (retval = 0)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ False ”
.

Definition ht_remove_safety_wit_5 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key <> key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_remove_safety_wit_6 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key <> key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_remove_safety_wit_7 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ False ”
.

Definition ht_remove_safety_wit_8 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ False ”
.

Definition ht_remove_safety_wit_9 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_remove_safety_wit_10 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_remove_safety_wit_11 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_remove_safety_wit_12 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ht_remove_safety_wit_13 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node = 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_remove_safety_wit_14 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node = 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |-> 0)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ht_remove_entail_wit_1 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (removed_pre <> 0)),
(  (storeK key_pre k )
  **  ((( &( "index" ) )) # UInt  |-> (retval % ( cap ) ))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (removed_pre <> 0) ”
  &&  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (removed_pre <> 0)),
(  TT && emp 
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ ((retval % ( cap ) ) < cap) ”
  &&  “ (0 <= (retval % ( cap ) )) ”
  &&  emp
).

Definition ht_remove_entail_wit_1_split_goal_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (removed_pre <> 0)),
  ((retval % ( cap ) ) < cap)
.

Definition ht_remove_entail_wit_1_split_goal_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (retval = (key_hash (k)))) (PreH2 : (0 <= (key_hash (k)))) (PreH3 : ((key_hash (k)) <= UINT_MAX)) (PreH4 : (0 < cap)) (PreH5 : ((Zlength (ptrs)) = cap)) (PreH6 : ((Zlength (buckets)) = cap)) (PreH7 : (key_eq_equiv key_eq )) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (h_pre <> 0)) (PreH13 : (removed_pre <> 0)),
  (0 <= (retval % ( cap ) ))
.

Definition ht_remove_entail_wit_2 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (removed_pre <> 0)),
(  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (node: Z) (pre: (@list (K * V))) (rest: (@list (K * V))),
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ ((Znth (((key_hash (k)) % ( cap ) )) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks ((key_hash (k)) % ( cap ) ) 0 cap ptrs )
  **  (((bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR)))) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR) ) ) (bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR))) pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) __default__List__Prod_K_V (PreH1 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH2 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH3 : (retval = (key_hash (k)))) (PreH4 : (0 <= (key_hash (k)))) (PreH5 : ((key_hash (k)) <= UINT_MAX)) (PreH6 : (0 < cap)) (PreH7 : ((Zlength (ptrs)) = cap)) (PreH8 : ((Zlength (buckets)) = cap)) (PreH9 : (key_eq_equiv key_eq )) (PreH10 : (key_eq_hash_compatible key_eq key_hash )) (PreH11 : (buckets_abs key_eq buckets m )) (PreH12 : (buckets_hash key_hash cap buckets )) (PreH13 : (buckets_unique key_eq buckets )) (PreH14 : (h_pre <> 0)) (PreH15 : (removed_pre <> 0)),
(  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) (Znth ((key_hash (k)) % ( cap ) ) buckets __default__List__Prod_K_V) )
  **  (storeK key_pre k )
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (pre: (@list (K * V))) (rest: (@list (K * V))),
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ ((Znth (((key_hash (k)) % ( cap ) )) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  (ht_bucket_chains_except storeK storeV ((key_hash (k)) % ( cap ) ) ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR) ) ) (bucks + (((key_hash (k)) % ( cap ) ) * sizeof(PTR))) pre )
  **  (ht_chain storeK storeV (Znth ((key_hash (k)) % ( cap ) ) ptrs 0) rest )
  **  (storeK key_pre k )
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
).

Definition ht_remove_entail_wit_3_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) (PreH1 : (key_eq k cur_k )) (PreH2 : (retval_3 = 1)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval_3 = 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (retval: Z),
(  “ ~((key_eq k cur_k )) ”
  &&  “ (retval = 0) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval = 0) ”
  &&  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_entail_wit_3_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : ~((key_eq k cur_k ))) (PreH2 : (retval = 0)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval = 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ ~((key_eq k cur_k )) ”
  &&  “ (retval = 0) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval = 0) ”
  &&  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_entail_wit_4_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_eq k cur_k )) (PreH2 : (retval = 1)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_entail_wit_4_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval_3: Z) (PreH1 : ~((key_eq k cur_k ))) (PreH2 : (retval_3 = 0)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval_3 <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (retval: Z),
(  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_entail_wit_5 :=
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node_2: Z) (node_ref: Z) (pre_2: (@list (K * V))) (rest_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : ~((key_eq k cur_k ))) (PreH2 : (retval = 0)) (PreH3 : (rest_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node_2 <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre_2) (rest_2)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre_2 ) -> ~((key_eq k pk )))) (PreH19 : (retval = 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node_2)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre_2 )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (node: Z) (pre: (@list (K * V))) (rest: (@list (K * V))),
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((&((node_2)  # "ht_node" ->ₛ "next")) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) &((node_2)  # "ht_node" ->ₛ "next") pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
) \/
(
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (key_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node_2: Z) (node_ref: Z) (pre_2: (@list (K * V))) (rest_2: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : ~((key_eq k cur_k ))) (PreH2 : (retval = 0)) (PreH3 : (rest_2 = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node_2 <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre_2) (rest_2)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre_2 ) -> ~((key_eq k pk )))) (PreH19 : (retval = 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node_2)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node_2)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((node_ref) # Ptr  |-> node_2)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre_2 )
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  EX (pre: (@list (K * V))) (rest: (@list (K * V))),
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) &((node_2)  # "ht_node" ->ₛ "next") pre )
  **  (ht_chain storeK storeV cur_next rest )
  **  (storeK key_pre k )
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
).

Definition ht_remove_return_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node = 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |-> 0)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
  (EX (new_m: (@mapping K V)) (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  “ (map_remove key_eq k m new_m ) ”
  &&  (storeV 0 v )
  **  ((removed_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre new_m ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (0 = 0) ”
  &&  ((removed_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_remove_return_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |-> 1)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  (EX (new_m: (@mapping K V)) (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  “ (map_remove key_eq k m new_m ) ”
  &&  (storeV cur_val v )
  **  ((removed_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre new_m ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (cur_val = 0) ”
  &&  ((removed_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_remove_return_wit_3 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |-> 1)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  (EX (new_m: (@mapping K V)) (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  “ (map_remove key_eq k m new_m ) ”
  &&  (storeV cur_val v )
  **  ((removed_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre new_m ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (cur_val = 0) ”
  &&  ((removed_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_remove_return_wit_4 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |-> 1)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
  (EX (new_m: (@mapping K V)) (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  “ (map_remove key_eq k m new_m ) ”
  &&  (storeV cur_val v )
  **  ((removed_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre new_m ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (cur_val = 0) ”
  &&  ((removed_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_remove_return_wit_5 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |-> 1)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  (EX (new_m: (@mapping K V)) (v: V),
  “ (map_get k m (Some (v)) ) ”
  &&  “ (map_remove key_eq k m new_m ) ”
  &&  (storeV cur_val v )
  **  ((removed_pre) # Int  |-> 1)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre new_m ))
  ||
  (“ (map_get k m None ) ”
  &&  “ (cur_val = 0) ”
  &&  ((removed_pre) # Int  |-> 0)
  **  (storeK key_pre k )
  **  (ht_store_map storeK storeV key_eq key_hash h_pre m ))
.

Definition ht_remove_partial_solve_wit_1 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (PreH1 : (h_pre <> 0)) (PreH2 : (removed_pre <> 0)),
  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
|--
  “ (h_pre <> 0) ”
  &&  “ (removed_pre <> 0) ”
  &&  (ht_store_map storeK storeV key_eq key_hash h_pre m )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
.

Definition ht_remove_partial_solve_wit_2 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)) (PreH10 : (removed_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_remove_partial_solve_wit_3 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (PreH1 : (0 < cap)) (PreH2 : ((Zlength (ptrs)) = cap)) (PreH3 : ((Zlength (buckets)) = cap)) (PreH4 : (key_eq_equiv key_eq )) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (h_pre <> 0)) (PreH10 : (removed_pre <> 0)),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (removed_pre <> 0) ”
  &&  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval =>
  (“ (retval = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_partial_solve_wit_4_pure :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)) (PreH16 : (removed_pre <> 0)),
(  ((( &( "index" ) )) # UInt  |-> ((key_hash (k)) % ( cap ) ))
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
.

Definition ht_remove_partial_solve_wit_4_aux :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (retval: Z) (PreH1 : (((key_hash (k)) % ( cap ) ) = ((key_hash (k)) % ( cap ) ))) (PreH2 : (0 <= ((key_hash (k)) % ( cap ) ))) (PreH3 : (((key_hash (k)) % ( cap ) ) < cap)) (PreH4 : (retval = (key_hash (k)))) (PreH5 : (0 <= (key_hash (k)))) (PreH6 : ((key_hash (k)) <= UINT_MAX)) (PreH7 : (0 < cap)) (PreH8 : ((Zlength (ptrs)) = cap)) (PreH9 : ((Zlength (buckets)) = cap)) (PreH10 : (key_eq_equiv key_eq )) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (h_pre <> 0)) (PreH16 : (removed_pre <> 0)),
(  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  (ht_bucket_chains storeK storeV ptrs buckets )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < (Zlength (ptrs))) ”
  &&  “ ((Zlength (ptrs)) = (Zlength (buckets))) ”
  &&  “ (0 <= ((key_hash (k)) % ( cap ) )) ”
  &&  “ (((key_hash (k)) % ( cap ) ) < cap) ”
  &&  “ (retval = (key_hash (k))) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ ((key_hash (k)) <= UINT_MAX) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (h_pre <> 0) ”
  &&  “ (removed_pre <> 0) ”
  &&  (ht_bucket_chains storeK storeV ptrs buckets )
  **  (storeK key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.full bucks cap ptrs )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec hash (fun F =>
ALL (key_k: K),
HoareFun ([ * void], u32)%ctype
  (fun arg_pre =>
  ((storeK arg_pre key_k )))
  (fun arg_pre retval_2 =>
  (“ (retval_2 = (key_hash (key_k))) ”
  &&  “ (0 <= (key_hash (key_k))) ”
  &&  “ ((key_hash (key_k)) <= UINT_MAX) ”
  &&  (storeK arg_pre key_k )))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_partial_solve_wit_4 := ht_remove_partial_solve_wit_4_pure -> ht_remove_partial_solve_wit_4_aux.

Definition ht_remove_partial_solve_wit_5 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node <> 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_remove_partial_solve_wit_6_pure :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node <> 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
  “ (node <> 0) ”
.

Definition ht_remove_partial_solve_wit_6_aux :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (PreH1 : (node <> 0)) (PreH2 : (0 < cap)) (PreH3 : ((Zlength (ptrs)) = cap)) (PreH4 : ((Zlength (buckets)) = cap)) (PreH5 : (key_eq_hash_compatible key_eq key_hash )) (PreH6 : (buckets_abs key_eq buckets m )) (PreH7 : (buckets_hash key_hash cap buckets )) (PreH8 : (buckets_unique key_eq buckets )) (PreH9 : (0 <= (key_hash (k)))) (PreH10 : (index = ((key_hash (k)) % ( cap ) ))) (PreH11 : (0 <= index)) (PreH12 : (index < cap)) (PreH13 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH14 : (key_eq_equiv key_eq )) (PreH15 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (ht_chain storeK storeV node rest )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (node <> 0) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  (ht_chain storeK storeV node rest )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_partial_solve_wit_6 := ht_remove_partial_solve_wit_6_pure -> ht_remove_partial_solve_wit_6_aux.

Definition ht_remove_partial_solve_wit_7 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (PreH1 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH2 : (node <> 0)) (PreH3 : (0 < cap)) (PreH4 : ((Zlength (ptrs)) = cap)) (PreH5 : ((Zlength (buckets)) = cap)) (PreH6 : (key_eq_hash_compatible key_eq key_hash )) (PreH7 : (buckets_abs key_eq buckets m )) (PreH8 : (buckets_hash key_hash cap buckets )) (PreH9 : (buckets_unique key_eq buckets )) (PreH10 : (0 <= (key_hash (k)))) (PreH11 : (index = ((key_hash (k)) % ( cap ) ))) (PreH12 : (0 <= index)) (PreH13 : (index < cap)) (PreH14 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH15 : (key_eq_equiv key_eq )) (PreH16 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))),
(  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  (storeK key_pre k )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> node)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_partial_solve_wit_8 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_eq k cur_k )) (PreH2 : (retval = 1)) (PreH3 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH4 : (node <> 0)) (PreH5 : (0 < cap)) (PreH6 : ((Zlength (ptrs)) = cap)) (PreH7 : ((Zlength (buckets)) = cap)) (PreH8 : (key_eq_hash_compatible key_eq key_hash )) (PreH9 : (buckets_abs key_eq buckets m )) (PreH10 : (buckets_hash key_hash cap buckets )) (PreH11 : (buckets_unique key_eq buckets )) (PreH12 : (0 <= (key_hash (k)))) (PreH13 : (index = ((key_hash (k)) % ( cap ) ))) (PreH14 : (0 <= index)) (PreH15 : (index < cap)) (PreH16 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH17 : (key_eq_equiv key_eq )) (PreH18 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH19 : (retval <> 0)),
(  ((( &( "result" ) )) # Ptr  |-> cur_val)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "index" ) )) # UInt  |-> index)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((( &( "node_ref" ) )) # Ptr  |-> node_ref)
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  TT && emp 
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))
.

Definition ht_remove_partial_solve_wit_9 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (key_free <> 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  (storeK cur_key cur_k )
  **  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_remove_partial_solve_wit_10 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free <> 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free <> 0)) (PreH4 : (store_exclusive storeK )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  (storeK key_pre k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (key_free <> 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK key_pre k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_remove_partial_solve_wit_11 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free = 0)) (PreH3 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (cur_key = key_pre) ”
  &&  “ (key_free = 0) ”
  &&  “ forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) ) ”
  &&  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Definition ht_remove_partial_solve_wit_12 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (cur_key = key_pre)) (PreH2 : (key_free <> 0)) (PreH3 : (store_exclusive storeK )) (PreH4 : (key_eq k cur_k )) (PreH5 : (retval = 1)) (PreH6 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH7 : (node <> 0)) (PreH8 : (0 < cap)) (PreH9 : ((Zlength (ptrs)) = cap)) (PreH10 : ((Zlength (buckets)) = cap)) (PreH11 : (key_eq_hash_compatible key_eq key_hash )) (PreH12 : (buckets_abs key_eq buckets m )) (PreH13 : (buckets_hash key_hash cap buckets )) (PreH14 : (buckets_unique key_eq buckets )) (PreH15 : (0 <= (key_hash (k)))) (PreH16 : (index = ((key_hash (k)) % ( cap ) ))) (PreH17 : (0 <= index)) (PreH18 : (index < cap)) (PreH19 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH20 : (key_eq_equiv key_eq )) (PreH21 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH22 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
|--
(  “ (cur_key = key_pre) ”
  &&  “ (key_free <> 0) ”
  &&  “ (store_exclusive storeK ) ”
  &&  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec key_free (fun F =>
ALL (k_2: K),
HoareFun ([ * void], void)%ctype
  (fun arg_pre =>
  ((storeK arg_pre k_2 )))
  (fun arg_pre (_retval : unit) =>
  (TT && emp ))
  F))
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free))))
.

Definition ht_remove_partial_solve_wit_13 :=
forall (V: Type) (K: Type) (k: K) (m: (@mapping K V)) (key_hash: (K -> Z)) (key_eq: (K -> (K -> Prop))) (storeV: (Z -> (V -> Assertion))) (storeK: (Z -> (K -> Assertion))) (h_pre: Z) (key_pre: Z) (removed_pre: Z) (hash: Z) (equal: Z) (key_free: Z) (value_free: Z) (bucks: Z) (ptrs: (@list Z)) (buckets: (@list (@list (K * V)))) (cap: Z) (node: Z) (node_ref: Z) (pre: (@list (K * V))) (rest: (@list (K * V))) (index: Z) (cur_next: Z) (cur_val: Z) (cur_key: Z) (cur_k: K) (cur_v: V) (rest_tail: (@list (K * V))) (retval: Z) (PreH1 : (key_free = 0)) (PreH2 : (cur_key <> key_pre)) (PreH3 : (key_free = 0)) (PreH4 : forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) )) (PreH5 : (key_eq k cur_k )) (PreH6 : (retval = 1)) (PreH7 : (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail)))) (PreH8 : (node <> 0)) (PreH9 : (0 < cap)) (PreH10 : ((Zlength (ptrs)) = cap)) (PreH11 : ((Zlength (buckets)) = cap)) (PreH12 : (key_eq_hash_compatible key_eq key_hash )) (PreH13 : (buckets_abs key_eq buckets m )) (PreH14 : (buckets_hash key_hash cap buckets )) (PreH15 : (buckets_unique key_eq buckets )) (PreH16 : (0 <= (key_hash (k)))) (PreH17 : (index = ((key_hash (k)) % ( cap ) ))) (PreH18 : (0 <= index)) (PreH19 : (index < cap)) (PreH20 : ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest)))) (PreH21 : (key_eq_equiv key_eq )) (PreH22 : forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk )))) (PreH23 : (retval <> 0)),
(  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
|--
(  “ (key_free = 0) ”
  &&  “ (cur_key <> key_pre) ”
  &&  “ (key_free = 0) ”
  &&  “ forall (x: Z), forall (k_2: K), (entails_emp (storeK (x) (k_2)) ) ”
  &&  “ (key_eq k cur_k ) ”
  &&  “ (retval = 1) ”
  &&  “ (rest = (cons ((pair (cur_k) (cur_v))) (rest_tail))) ”
  &&  “ (node <> 0) ”
  &&  “ (0 < cap) ”
  &&  “ ((Zlength (ptrs)) = cap) ”
  &&  “ ((Zlength (buckets)) = cap) ”
  &&  “ (key_eq_hash_compatible key_eq key_hash ) ”
  &&  “ (buckets_abs key_eq buckets m ) ”
  &&  “ (buckets_hash key_hash cap buckets ) ”
  &&  “ (buckets_unique key_eq buckets ) ”
  &&  “ (0 <= (key_hash (k))) ”
  &&  “ (index = ((key_hash (k)) % ( cap ) )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < cap) ”
  &&  “ ((Znth (index) (buckets) ((@nil (K * V)))) = (app (pre) (rest))) ”
  &&  “ (key_eq_equiv key_eq ) ”
  &&  “ forall (pk: K), forall (pv: V), ((In (pair (pk) (pv)) pre ) -> ~((key_eq k pk ))) ”
  &&  “ (retval <> 0) ”
  &&  ((&((node)  # "ht_node" ->ₛ "key")) # Ptr  |-> cur_key)
  **  ((&((node)  # "ht_node" ->ₛ "val")) # Ptr  |-> cur_val)
  **  ((&((node)  # "ht_node" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (storeK key_pre k )
  **  (storeK cur_key cur_k )
  **  (storeV cur_val cur_v )
  **  (ht_chain storeK storeV cur_next rest_tail )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "hash")) # Ptr  |-> hash)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "equal")) # Ptr  |-> equal)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "key_free")) # Ptr  |-> key_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "value_free")) # Ptr  |-> value_free)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "capacity")) # UInt  |-> cap)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks)
  **  (PtrArray.missing_i bucks index 0 cap ptrs )
  **  ((node_ref) # Ptr  |-> cur_next)
  **  (ht_bucket_chains_except storeK storeV index ptrs buckets )
  **  (ht_chain_bseg storeK storeV (bucks + (index * sizeof(PTR) ) ) node_ref pre )
  **  ((removed_pre) # Int  |->_)
&&
((func_ptr_spec equal (fun F =>
ALL (lhs_k: K),
ALL (rhs_k: K),
HoareFun ([ * void;  * void], u32)%ctype
  (fun '(lhs_pre, rhs_pre) =>
  ((storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k )))
  (fun '(lhs_pre, rhs_pre) retval_2 =>
(orp
  (“ (key_eq lhs_k rhs_k ) ”
  &&  “ (retval_2 = 1) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))
  (“ ~((key_eq lhs_k rhs_k )) ”
  &&  “ (retval_2 = 0) ”
  &&  (storeK lhs_pre lhs_k )
  **  (storeK rhs_pre rhs_k ))))
  F))
&&
(ht_specs storeK storeV key_hash key_eq hash equal key_free value_free)))
.

Module Type VC_Correct.


Axiom proof_of_entails_emp_unfold_return_wit_1 : entails_emp_unfold_return_wit_1.
Axiom proof_of_ht_specs_get_hash_spec_return_wit_1 : ht_specs_get_hash_spec_return_wit_1.
Axiom proof_of_ht_specs_get_equal_spec_return_wit_1 : ht_specs_get_equal_spec_return_wit_1.
Axiom proof_of_ht_specs_get_key_free_spec_return_wit_1 : ht_specs_get_key_free_spec_return_wit_1.
Axiom proof_of_ht_specs_get_value_free_spec_return_wit_1 : ht_specs_get_value_free_spec_return_wit_1.
Axiom proof_of_ht_store_map_unfold_return_wit_1 : ht_store_map_unfold_return_wit_1.
Axiom proof_of_ht_bucket_chains_split_Znth_return_wit_1 : ht_bucket_chains_split_Znth_return_wit_1.
Axiom proof_of_ht_chain_nonnull_unfold_return_wit_1 : ht_chain_nonnull_unfold_return_wit_1.
Axiom proof_of_ht_ptr_equal_safety_wit_1 : ht_ptr_equal_safety_wit_1.
Axiom proof_of_ht_ptr_equal_safety_wit_2 : ht_ptr_equal_safety_wit_2.
Axiom proof_of_ht_ptr_equal_return_wit_1 : ht_ptr_equal_return_wit_1.
Axiom proof_of_ht_ptr_equal_return_wit_2 : ht_ptr_equal_return_wit_2.
Axiom proof_of_ht_int_hash_safety_wit_1 : ht_int_hash_safety_wit_1.
Axiom proof_of_ht_int_hash_safety_wit_2 : ht_int_hash_safety_wit_2.
Axiom proof_of_ht_int_hash_return_wit_1 : ht_int_hash_return_wit_1.
Axiom proof_of_ht_init_return_wit_1 : ht_init_return_wit_1.
Axiom proof_of_ht_init_partial_solve_wit_1_pure : ht_init_partial_solve_wit_1_pure.
Axiom proof_of_ht_init_partial_solve_wit_1 : ht_init_partial_solve_wit_1.
Axiom proof_of_ht_add_safety_wit_1 : ht_add_safety_wit_1.
Axiom proof_of_ht_add_safety_wit_2 : ht_add_safety_wit_2.
Axiom proof_of_ht_add_safety_wit_3 : ht_add_safety_wit_3.
Axiom proof_of_ht_add_safety_wit_4 : ht_add_safety_wit_4.
Axiom proof_of_ht_add_safety_wit_5 : ht_add_safety_wit_5.
Axiom proof_of_ht_add_safety_wit_6 : ht_add_safety_wit_6.
Axiom proof_of_ht_add_safety_wit_7 : ht_add_safety_wit_7.
Axiom proof_of_ht_add_safety_wit_8 : ht_add_safety_wit_8.
Axiom proof_of_ht_add_safety_wit_9 : ht_add_safety_wit_9.
Axiom proof_of_ht_add_safety_wit_10 : ht_add_safety_wit_10.
Axiom proof_of_ht_add_safety_wit_11 : ht_add_safety_wit_11.
Axiom proof_of_ht_add_safety_wit_12 : ht_add_safety_wit_12.
Axiom proof_of_ht_add_safety_wit_13 : ht_add_safety_wit_13.
Axiom proof_of_ht_add_safety_wit_14 : ht_add_safety_wit_14.
Axiom proof_of_ht_add_safety_wit_15 : ht_add_safety_wit_15.
Axiom proof_of_ht_add_safety_wit_16 : ht_add_safety_wit_16.
Axiom proof_of_ht_add_safety_wit_17 : ht_add_safety_wit_17.
Axiom proof_of_ht_add_safety_wit_18 : ht_add_safety_wit_18.
Axiom proof_of_ht_add_safety_wit_19 : ht_add_safety_wit_19.
Axiom proof_of_ht_add_safety_wit_20 : ht_add_safety_wit_20.
Axiom proof_of_ht_add_safety_wit_21 : ht_add_safety_wit_21.
Axiom proof_of_ht_add_safety_wit_22 : ht_add_safety_wit_22.
Axiom proof_of_ht_add_safety_wit_23 : ht_add_safety_wit_23.
Axiom proof_of_ht_add_safety_wit_24 : ht_add_safety_wit_24.
Axiom proof_of_ht_add_entail_wit_1 : ht_add_entail_wit_1.
Axiom proof_of_ht_add_entail_wit_2 : ht_add_entail_wit_2.
Axiom proof_of_ht_add_entail_wit_3_1 : ht_add_entail_wit_3_1.
Axiom proof_of_ht_add_entail_wit_3_2 : ht_add_entail_wit_3_2.
Axiom proof_of_ht_add_entail_wit_4_1 : ht_add_entail_wit_4_1.
Axiom proof_of_ht_add_entail_wit_4_2 : ht_add_entail_wit_4_2.
Axiom proof_of_ht_add_entail_wit_5 : ht_add_entail_wit_5.
Axiom proof_of_ht_add_return_wit_1 : ht_add_return_wit_1.
Axiom proof_of_ht_add_return_wit_2 : ht_add_return_wit_2.
Axiom proof_of_ht_add_return_wit_3 : ht_add_return_wit_3.
Axiom proof_of_ht_add_return_wit_4 : ht_add_return_wit_4.
Axiom proof_of_ht_add_return_wit_5 : ht_add_return_wit_5.
Axiom proof_of_ht_add_return_wit_6 : ht_add_return_wit_6.
Axiom proof_of_ht_add_return_wit_7 : ht_add_return_wit_7.
Axiom proof_of_ht_add_return_wit_8 : ht_add_return_wit_8.
Axiom proof_of_ht_add_return_wit_9 : ht_add_return_wit_9.
Axiom proof_of_ht_add_return_wit_10 : ht_add_return_wit_10.
Axiom proof_of_ht_add_return_wit_11 : ht_add_return_wit_11.
Axiom proof_of_ht_add_return_wit_12 : ht_add_return_wit_12.
Axiom proof_of_ht_add_return_wit_13 : ht_add_return_wit_13.
Axiom proof_of_ht_add_return_wit_14 : ht_add_return_wit_14.
Axiom proof_of_ht_add_return_wit_15 : ht_add_return_wit_15.
Axiom proof_of_ht_add_return_wit_16 : ht_add_return_wit_16.
Axiom proof_of_ht_add_return_wit_17 : ht_add_return_wit_17.
Axiom proof_of_ht_add_partial_solve_wit_1 : ht_add_partial_solve_wit_1.
Axiom proof_of_ht_add_partial_solve_wit_2 : ht_add_partial_solve_wit_2.
Axiom proof_of_ht_add_partial_solve_wit_3 : ht_add_partial_solve_wit_3.
Axiom proof_of_ht_add_partial_solve_wit_4_pure : ht_add_partial_solve_wit_4_pure.
Axiom proof_of_ht_add_partial_solve_wit_4 : ht_add_partial_solve_wit_4.
Axiom proof_of_ht_add_partial_solve_wit_5 : ht_add_partial_solve_wit_5.
Axiom proof_of_ht_add_partial_solve_wit_6 : ht_add_partial_solve_wit_6.
Axiom proof_of_ht_add_partial_solve_wit_7 : ht_add_partial_solve_wit_7.
Axiom proof_of_ht_add_partial_solve_wit_8_pure : ht_add_partial_solve_wit_8_pure.
Axiom proof_of_ht_add_partial_solve_wit_8 : ht_add_partial_solve_wit_8.
Axiom proof_of_ht_add_partial_solve_wit_9 : ht_add_partial_solve_wit_9.
Axiom proof_of_ht_add_partial_solve_wit_10 : ht_add_partial_solve_wit_10.
Axiom proof_of_ht_add_partial_solve_wit_11 : ht_add_partial_solve_wit_11.
Axiom proof_of_ht_add_partial_solve_wit_12 : ht_add_partial_solve_wit_12.
Axiom proof_of_ht_add_partial_solve_wit_13 : ht_add_partial_solve_wit_13.
Axiom proof_of_ht_add_partial_solve_wit_14 : ht_add_partial_solve_wit_14.
Axiom proof_of_ht_add_partial_solve_wit_15 : ht_add_partial_solve_wit_15.
Axiom proof_of_ht_add_partial_solve_wit_16 : ht_add_partial_solve_wit_16.
Axiom proof_of_ht_add_partial_solve_wit_17 : ht_add_partial_solve_wit_17.
Axiom proof_of_ht_add_partial_solve_wit_18 : ht_add_partial_solve_wit_18.
Axiom proof_of_ht_add_partial_solve_wit_19 : ht_add_partial_solve_wit_19.
Axiom proof_of_ht_add_partial_solve_wit_20 : ht_add_partial_solve_wit_20.
Axiom proof_of_ht_add_partial_solve_wit_21 : ht_add_partial_solve_wit_21.
Axiom proof_of_ht_add_partial_solve_wit_22 : ht_add_partial_solve_wit_22.
Axiom proof_of_ht_add_which_implies_wit_1 : ht_add_which_implies_wit_1.
Axiom proof_of_ht_find_safety_wit_1 : ht_find_safety_wit_1.
Axiom proof_of_ht_find_safety_wit_2 : ht_find_safety_wit_2.
Axiom proof_of_ht_find_safety_wit_3 : ht_find_safety_wit_3.
Axiom proof_of_ht_find_safety_wit_4 : ht_find_safety_wit_4.
Axiom proof_of_ht_find_safety_wit_5 : ht_find_safety_wit_5.
Axiom proof_of_ht_find_safety_wit_6 : ht_find_safety_wit_6.
Axiom proof_of_ht_find_safety_wit_7 : ht_find_safety_wit_7.
Axiom proof_of_ht_find_entail_wit_1 : ht_find_entail_wit_1.
Axiom proof_of_ht_find_entail_wit_2 : ht_find_entail_wit_2.
Axiom proof_of_ht_find_entail_wit_3_1 : ht_find_entail_wit_3_1.
Axiom proof_of_ht_find_entail_wit_3_2 : ht_find_entail_wit_3_2.
Axiom proof_of_ht_find_entail_wit_4_1 : ht_find_entail_wit_4_1.
Axiom proof_of_ht_find_entail_wit_4_2 : ht_find_entail_wit_4_2.
Axiom proof_of_ht_find_entail_wit_5 : ht_find_entail_wit_5.
Axiom proof_of_ht_find_return_wit_1 : ht_find_return_wit_1.
Axiom proof_of_ht_find_return_wit_2 : ht_find_return_wit_2.
Axiom proof_of_ht_find_partial_solve_wit_1 : ht_find_partial_solve_wit_1.
Axiom proof_of_ht_find_partial_solve_wit_2 : ht_find_partial_solve_wit_2.
Axiom proof_of_ht_find_partial_solve_wit_3 : ht_find_partial_solve_wit_3.
Axiom proof_of_ht_find_partial_solve_wit_4_pure : ht_find_partial_solve_wit_4_pure.
Axiom proof_of_ht_find_partial_solve_wit_4 : ht_find_partial_solve_wit_4.
Axiom proof_of_ht_find_partial_solve_wit_5 : ht_find_partial_solve_wit_5.
Axiom proof_of_ht_find_partial_solve_wit_6 : ht_find_partial_solve_wit_6.
Axiom proof_of_ht_find_partial_solve_wit_7 : ht_find_partial_solve_wit_7.
Axiom proof_of_ht_find_partial_solve_wit_8_pure : ht_find_partial_solve_wit_8_pure.
Axiom proof_of_ht_find_partial_solve_wit_8 : ht_find_partial_solve_wit_8.
Axiom proof_of_ht_find_partial_solve_wit_9 : ht_find_partial_solve_wit_9.
Axiom proof_of_ht_find_which_implies_wit_1 : ht_find_which_implies_wit_1.
Axiom proof_of_ht_remove_safety_wit_1 : ht_remove_safety_wit_1.
Axiom proof_of_ht_remove_safety_wit_2 : ht_remove_safety_wit_2.
Axiom proof_of_ht_remove_safety_wit_3 : ht_remove_safety_wit_3.
Axiom proof_of_ht_remove_safety_wit_4 : ht_remove_safety_wit_4.
Axiom proof_of_ht_remove_safety_wit_5 : ht_remove_safety_wit_5.
Axiom proof_of_ht_remove_safety_wit_6 : ht_remove_safety_wit_6.
Axiom proof_of_ht_remove_safety_wit_7 : ht_remove_safety_wit_7.
Axiom proof_of_ht_remove_safety_wit_8 : ht_remove_safety_wit_8.
Axiom proof_of_ht_remove_safety_wit_9 : ht_remove_safety_wit_9.
Axiom proof_of_ht_remove_safety_wit_10 : ht_remove_safety_wit_10.
Axiom proof_of_ht_remove_safety_wit_11 : ht_remove_safety_wit_11.
Axiom proof_of_ht_remove_safety_wit_12 : ht_remove_safety_wit_12.
Axiom proof_of_ht_remove_safety_wit_13 : ht_remove_safety_wit_13.
Axiom proof_of_ht_remove_safety_wit_14 : ht_remove_safety_wit_14.
Axiom proof_of_ht_remove_entail_wit_1 : ht_remove_entail_wit_1.
Axiom proof_of_ht_remove_entail_wit_2 : ht_remove_entail_wit_2.
Axiom proof_of_ht_remove_entail_wit_3_1 : ht_remove_entail_wit_3_1.
Axiom proof_of_ht_remove_entail_wit_3_2 : ht_remove_entail_wit_3_2.
Axiom proof_of_ht_remove_entail_wit_4_1 : ht_remove_entail_wit_4_1.
Axiom proof_of_ht_remove_entail_wit_4_2 : ht_remove_entail_wit_4_2.
Axiom proof_of_ht_remove_entail_wit_5 : ht_remove_entail_wit_5.
Axiom proof_of_ht_remove_return_wit_1 : ht_remove_return_wit_1.
Axiom proof_of_ht_remove_return_wit_2 : ht_remove_return_wit_2.
Axiom proof_of_ht_remove_return_wit_3 : ht_remove_return_wit_3.
Axiom proof_of_ht_remove_return_wit_4 : ht_remove_return_wit_4.
Axiom proof_of_ht_remove_return_wit_5 : ht_remove_return_wit_5.
Axiom proof_of_ht_remove_partial_solve_wit_1 : ht_remove_partial_solve_wit_1.
Axiom proof_of_ht_remove_partial_solve_wit_2 : ht_remove_partial_solve_wit_2.
Axiom proof_of_ht_remove_partial_solve_wit_3 : ht_remove_partial_solve_wit_3.
Axiom proof_of_ht_remove_partial_solve_wit_4_pure : ht_remove_partial_solve_wit_4_pure.
Axiom proof_of_ht_remove_partial_solve_wit_4 : ht_remove_partial_solve_wit_4.
Axiom proof_of_ht_remove_partial_solve_wit_5 : ht_remove_partial_solve_wit_5.
Axiom proof_of_ht_remove_partial_solve_wit_6_pure : ht_remove_partial_solve_wit_6_pure.
Axiom proof_of_ht_remove_partial_solve_wit_6 : ht_remove_partial_solve_wit_6.
Axiom proof_of_ht_remove_partial_solve_wit_7 : ht_remove_partial_solve_wit_7.
Axiom proof_of_ht_remove_partial_solve_wit_8 : ht_remove_partial_solve_wit_8.
Axiom proof_of_ht_remove_partial_solve_wit_9 : ht_remove_partial_solve_wit_9.
Axiom proof_of_ht_remove_partial_solve_wit_10 : ht_remove_partial_solve_wit_10.
Axiom proof_of_ht_remove_partial_solve_wit_11 : ht_remove_partial_solve_wit_11.
Axiom proof_of_ht_remove_partial_solve_wit_12 : ht_remove_partial_solve_wit_12.
Axiom proof_of_ht_remove_partial_solve_wit_13 : ht_remove_partial_solve_wit_13.

End VC_Correct.
