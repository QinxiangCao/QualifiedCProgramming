From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Record Recordhashtbl : Type := make_record_hashtbl {
  hashtbl_hash : Z;
  hashtbl_equal : Z;
  hashtbl_key_free : Z;
  hashtbl_value_free : Z;
  hashtbl_capacity : Z;
  hashtbl_bucks : Z
}.

Definition zero_record_hashtbl : Recordhashtbl :=
  make_record_hashtbl 0 0 0 0 0 0.

Definition StructPredhashtbl (x : Z) (v : Recordhashtbl) : Assertion :=
  ((&(x # "hashtbl" ->ₛ "hash")) # Ptr  |-> v.(hashtbl_hash)) **
  ((&(x # "hashtbl" ->ₛ "equal")) # Ptr  |-> v.(hashtbl_equal)) **
  ((&(x # "hashtbl" ->ₛ "key_free")) # Ptr  |-> v.(hashtbl_key_free)) **
  ((&(x # "hashtbl" ->ₛ "value_free")) # Ptr  |-> v.(hashtbl_value_free)) **
  ((&(x # "hashtbl" ->ₛ "capacity")) # UInt  |-> v.(hashtbl_capacity)) **
  ((&(x # "hashtbl" ->ₛ "bucks")) # Ptr  |-> v.(hashtbl_bucks)).

Definition UndefStructPredhashtbl (x : Z) : Assertion :=
  ((&(x # "hashtbl" ->ₛ "hash")) # Ptr  |->_) **
  ((&(x # "hashtbl" ->ₛ "equal")) # Ptr  |->_) **
  ((&(x # "hashtbl" ->ₛ "key_free")) # Ptr  |->_) **
  ((&(x # "hashtbl" ->ₛ "value_free")) # Ptr  |->_) **
  ((&(x # "hashtbl" ->ₛ "capacity")) # UInt  |->_) **
  ((&(x # "hashtbl" ->ₛ "bucks")) # Ptr  |->_).

Lemma store_Predhashtbl_to_undef : forall x v,
  StructPredhashtbl x v |-- UndefStructPredhashtbl x.
Proof.
  intros.
  unfold StructPredhashtbl, UndefStructPredhashtbl.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_uint_undef_store_uint.
  sep_apply store_ptr_undef_store_ptr.
  cancel.
Qed.

Lemma undefstore_Predhashtbl_to_align : forall x,
  UndefStructPredhashtbl x |-- store_align_n ((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR)).
Proof.
  intros.
  unfold UndefStructPredhashtbl.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_uint_align4.
  sep_apply undef_store_ptr_align.
  sep_apply store_align4_to_store_align.
  sep_apply (store_align_merge (sizeof(PTR)) (sizeof(PTR))).
  sep_apply (store_align_merge ((sizeof(PTR) + sizeof(PTR))) (sizeof(PTR))).
  sep_apply (store_align_merge (((sizeof(PTR) + sizeof(PTR)) + sizeof(PTR))) (sizeof(PTR))).
  sep_apply (store_align_merge ((((sizeof(PTR) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR))) (4 * 1)).
  sep_apply (store_align_merge (((((sizeof(PTR) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + 4 * 1)) (sizeof(PTR))).
  replace (((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR))) with ((((((sizeof(PTR) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + 4 * 1) + sizeof(PTR))) by
    (simpl_nonptr_sizeof; ring).
  cancel.
Qed.

Lemma store_Predhashtbl_to_align : forall x v,
  StructPredhashtbl x v |-- store_align_n ((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(UINT)) + sizeof(PTR)).
Proof.
  intros.
  sep_apply store_Predhashtbl_to_undef.
  sep_apply undefstore_Predhashtbl_to_align.
  cancel.
Qed.

Record Recordht_node : Type := make_record_ht_node {
  ht_node_key : Z;
  ht_node_val : Z;
  ht_node_next : Z
}.

Definition zero_record_ht_node : Recordht_node :=
  make_record_ht_node 0 0 0.

Definition StructPredht_node (x : Z) (v : Recordht_node) : Assertion :=
  ((&(x # "ht_node" ->ₛ "key")) # Ptr  |-> v.(ht_node_key)) **
  ((&(x # "ht_node" ->ₛ "val")) # Ptr  |-> v.(ht_node_val)) **
  ((&(x # "ht_node" ->ₛ "next")) # Ptr  |-> v.(ht_node_next)).

Definition UndefStructPredht_node (x : Z) : Assertion :=
  ((&(x # "ht_node" ->ₛ "key")) # Ptr  |->_) **
  ((&(x # "ht_node" ->ₛ "val")) # Ptr  |->_) **
  ((&(x # "ht_node" ->ₛ "next")) # Ptr  |->_).

Lemma store_Predht_node_to_undef : forall x v,
  StructPredht_node x v |-- UndefStructPredht_node x.
Proof.
  intros.
  unfold StructPredht_node, UndefStructPredht_node.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  cancel.
Qed.

Lemma undefstore_Predht_node_to_align : forall x,
  UndefStructPredht_node x |-- store_align_n (((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)).
Proof.
  intros.
  unfold UndefStructPredht_node.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply undef_store_ptr_align.
  sep_apply (store_align_merge (sizeof(PTR)) (sizeof(PTR))).
  sep_apply (store_align_merge ((sizeof(PTR) + sizeof(PTR))) (sizeof(PTR))).
  replace ((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR))) with (((sizeof(PTR) + sizeof(PTR)) + sizeof(PTR))) by
    (simpl_nonptr_sizeof; ring).
  cancel.
Qed.

Lemma store_Predht_node_to_align : forall x v,
  StructPredht_node x v |-- store_align_n (((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)).
Proof.
  intros.
  sep_apply store_Predht_node_to_undef.
  sep_apply undefstore_Predht_node_to_align.
  cancel.
Qed.

