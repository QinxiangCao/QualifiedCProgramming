From SimpleC.Verification Require Import VCPrelude.
Require Import ListLib.Base.Positional.
From SimpleC.Common Require Import CTypes.
From SimpleC.CoreLang Require Import CTypes.
From MonadLib.MonadErr Require Import MonadErrBasic.

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.ClassicalChoice.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import ListNotations.
Import List.
Import ListLib.Base.Positional.
Import naive_C_Rules.
Local Open Scope sac.

Definition entails_emp (A : Assertion) : Prop := A |-- emp.

Definition store_exclusive {A : Type}
    (store : Z -> A -> Assertion) : Prop :=
  forall p x y, store p x ** store p y |-- “ False ”.

Definition mapping (K V : Type) : Type := K -> option V.

Definition empty_mapping {K V : Type} : mapping K V :=
  fun _ => None.

Definition map_empty {K V : Type} (m : mapping K V) : Prop :=
  forall k, m k = None.

Definition map_get {K V : Type}
           (k : K) (m : mapping K V) (result : option V) : Prop :=
  m k = result.

Definition map_insert {K V : Type}
           (key_eq : K -> K -> Prop) (k : K) (v : V)
           (before after : mapping K V) : Prop :=
  forall query,
    (key_eq query k -> after query = Some v) /\
    (~ key_eq query k -> after query = before query).

Definition map_remove {K V : Type}
           (key_eq : K -> K -> Prop) (k : K)
           (before after : mapping K V) : Prop :=
  forall query,
    (key_eq query k -> after query = None) /\
    (~ key_eq query k -> after query = before query).


Section HashTable.
Context {K V : Type}.
Context (storeK : Z -> K -> Assertion) (storeV : Z -> V -> Assertion).

Definition key_eq_hash_compatible
    (key_eq : K -> K -> Prop) (key_hash : K -> Z) : Prop :=
  forall a b, key_eq a b -> key_hash a = key_hash b.

Definition key_eq_equiv (key_eq : K -> K -> Prop) : Prop :=
  Equivalence key_eq.

Definition ht_hash_spec (key_hash : K -> Z) (hash : Z) : Assertion :=
  func_ptr_spec hash (fun F =>
    ALL k : K,
    HoareFun ( [ *void ], u32 )%ctype
      (fun key =>
        storeK key k)
      (fun key retval =>
        storeK key k &&
        “ 0 <= key_hash k /\ key_hash k <= UINT_MAX /\
          retval = key_hash k ”)
      F).

Definition ht_equal_spec
    (key_eq : K -> K -> Prop) (equal : Z) : Assertion :=
  func_ptr_spec equal (fun F =>
    ALL a : K,
    ALL b : K,
    HoareFun ( [ *void ; *void ], u32 )%ctype
      (fun '(x, y) =>
        storeK x a ** storeK y b)
      (fun '(x, y) retval =>
        storeK x a ** storeK y b &&
        (orp
          (“ key_eq a b ” && “ retval = 1 ”)
          (“ ~ key_eq a b ” && “ retval = 0 ”)))
      F).

Definition ht_free_spec {A : Type}
    (storeA : Z -> A -> Assertion) (free_fn : Z) : Assertion :=
  “ free_fn = 0 /\ forall x a, entails_emp (storeA x a) ” ||
  (“ store_exclusive storeA ” && func_ptr_spec free_fn (fun F =>
    ALL a : A,
    HoareFun ( [ *void ], void )%ctype
      (fun arg =>
        storeA arg a)
      (fun arg retval =>
        emp)
      F)).

Definition ht_specs (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    (hash equal key_free value_free : Z) : Assertion :=
  ht_hash_spec key_hash hash &&
  ht_equal_spec key_eq equal &&
  ht_free_spec storeK key_free &&
  ht_free_spec storeV value_free.

Lemma ht_hash_spec_corable
    (key_hash : K -> Z) hash :
  corable (ht_hash_spec key_hash hash).
Proof.
  apply func_ptr_spec_corable; intros.
  apply allp_corable; intros.
  apply HoareFun_corable.
Qed.

Lemma ht_equal_spec_corable
    (key_eq : K -> K -> Prop) equal :
  corable (ht_equal_spec key_eq equal).
Proof.
  apply func_ptr_spec_corable; intros.
  repeat (simple apply allp_corable; intros).
  apply HoareFun_corable.
Qed.

Lemma ht_free_spec_corable
    {A : Type} (storeA : Z -> A -> Assertion) free_fn :
  corable (ht_free_spec storeA free_fn).
Proof.
  apply corable_orp; [apply corable_coq_prop |].
  apply corable_andp; [apply corable_coq_prop |].
  apply func_ptr_spec_corable; intros.
  repeat (simple apply allp_corable; intros).
  apply HoareFun_corable.
Qed.

Lemma ht_specs_corable
    (key_hash : K -> Z) (key_eq : K -> K -> Prop)
    (hash equal key_free value_free : Z) :
  corable (ht_specs key_hash key_eq hash equal key_free value_free).
Proof.
  unfold ht_specs.
  repeat simple apply corable_andp.
  - apply ht_hash_spec_corable.
  - apply ht_equal_spec_corable.
  - apply ht_free_spec_corable.
  - apply ht_free_spec_corable.
Qed.

Fixpoint kvs_abs (key_eq : K -> K -> Prop)
    (items : list (K * V)) (m : mapping K V) : Prop :=
  match items with
  | nil => map_empty m
  | (k, v) :: rest =>
      exists rest_map,
        kvs_abs key_eq rest rest_map /\
        map_insert key_eq k v rest_map m
  end.

Definition buckets_abs (key_eq : K -> K -> Prop)
    (buckets : list (list (K * V)))
    (m : mapping K V) : Prop :=
  kvs_abs key_eq (List.concat buckets) m.

Fixpoint kvs_unique (key_eq : K -> K -> Prop)
    (items : list (K * V)) : Prop :=
  match items with
  | nil => True
  | (k, _) :: rest =>
      (forall k' v', In (k', v') rest -> ~ key_eq k k') /\
      kvs_unique key_eq rest
  end.

Definition buckets_unique (key_eq : K -> K -> Prop)
    (buckets : list (list (K * V))) : Prop :=
  kvs_unique key_eq (List.concat buckets).

Definition buckets_hash (key_hash : K -> Z)
    (cap : Z) (buckets : list (list (K * V))) : Prop :=
  forall idx k v,
    0 <= idx < cap ->
    In (k, v) (Znth idx buckets nil) ->
    key_hash k mod cap = idx.


Fixpoint ht_chain_seg (p q : Z) (bucket : list (K * V)) :=
  match bucket with
  | nil => “ p = q ” && emp
  | (k, v) :: rest =>
      “ p <> 0 ” &&
      EX key val next : Z,
        &(p # "ht_node" ->ₛ "key") # Ptr |-> key **
        &(p # "ht_node" ->ₛ "val") # Ptr |-> val **
        &(p # "ht_node" ->ₛ "next") # Ptr |-> next **
        storeK key k **
        storeV val v **
        ht_chain_seg next q rest
  end.

Definition ht_chain (p : Z) (bucket : list (K * V)) :=
  ht_chain_seg p 0 bucket.

Fixpoint ht_chain_bseg
    (slot end_slot : Z) (bucket : list (K * V)) : Assertion :=
  match bucket with
  | nil => “ slot = end_slot ” && emp
  | (k, v) :: rest =>
      EX node key val : Z,
        “ node <> 0 ” &&
        slot # Ptr |-> node **
        &(node # "ht_node" ->ₛ "key") # Ptr |-> key **
        &(node # "ht_node" ->ₛ "val") # Ptr |-> val **
        storeK key k **
        storeV val v **
        ht_chain_bseg (&(node # "ht_node" ->ₛ "next")) end_slot rest
  end.

Definition ht_chain_value_hole
    (key_eq : K -> K -> Prop) (query_k : K)
    (p value : Z) (bucket : list (K * V)) :=
  EX pre : list (K * V),
  EX hit_k : K, EX old_v : V,
  EX post : list (K * V),
  EX hit_node key next : Z,
    “ bucket = pre ++ (hit_k, old_v) :: post /\
      key_eq query_k hit_k /\
      hit_node <> 0 ” &&
    ht_chain_seg p hit_node pre **
    &(hit_node # "ht_node" ->ₛ "key") # Ptr |-> key **
    &(hit_node # "ht_node" ->ₛ "val") # Ptr |-> value **
    &(hit_node # "ht_node" ->ₛ "next") # Ptr |-> next **
    storeK key hit_k **
    ht_chain next post.

Definition ht_chain_node_ref_hole
    (key_eq : K -> K -> Prop) (query_k : K)
    (start_slot hit_slot next : Z) (bucket : list (K * V)) :=
  EX pre : list (K * V),
  EX hit_k : K, EX old_v : V,
  EX post : list (K * V),
    “ hit_slot <> 0 /\
      bucket = pre ++ (hit_k, old_v) :: post /\
      key_eq query_k hit_k /\
      (forall pk pv, In (pk, pv) pre -> ~ key_eq query_k pk) ” &&
    ht_chain_bseg start_slot hit_slot pre **
    ht_chain next post.

Definition ht_bucket_chains (ptrs : list Z) buckets :=
  iter_sepcon
    (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets)).

Definition ht_bucket_chains_except (idx : Z) ptrs buckets :=
  iter_sepcon
    (map (fun '(p, bucket) => ht_chain p bucket)
         (remove_Znth idx (combine ptrs buckets))).

Definition ht_bucket_chains_value_hole
    (key_eq : K -> K -> Prop) (query_k : K)
    (idx : Z) (value : Z)
    (ptrs : list Z) (buckets : list (list (K * V))) : Assertion :=
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain_value_hole
    key_eq query_k
    (Znth idx ptrs 0)
    value
    (Znth idx buckets nil).


Definition ht_store
    (h hash equal key_free value_free cap bucks : Z)
    (buckets : list (list (K * V))) : Assertion :=
  EX ptrs : list Z,
    “ 0 < cap /\
      Zlength ptrs = cap /\
      Zlength buckets = cap ” &&
    &(h # "hashtbl" ->ₛ "hash") # Ptr |-> hash **
    &(h # "hashtbl" ->ₛ "equal") # Ptr |-> equal **
    &(h # "hashtbl" ->ₛ "key_free") # Ptr |-> key_free **
    &(h # "hashtbl" ->ₛ "value_free") # Ptr |-> value_free **
    &(h # "hashtbl" ->ₛ "capacity") # UInt |-> cap **
    &(h # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks **
    PtrArray.full bucks cap ptrs **
    ht_bucket_chains ptrs buckets.

Definition ht_store_value_hole
    (key_eq : K -> K -> Prop) (query_k : K)
    (idx : Z) (value : Z)
    (h hash equal key_free value_free cap bucks : Z)
    (buckets : list (list (K * V))) : Assertion :=
  EX ptrs : list Z,
    “ 0 < cap /\
      Zlength ptrs = cap /\
      Zlength buckets = cap ” &&
    &(h # "hashtbl" ->ₛ "hash") # Ptr |-> hash **
    &(h # "hashtbl" ->ₛ "equal") # Ptr |-> equal **
    &(h # "hashtbl" ->ₛ "key_free") # Ptr |-> key_free **
    &(h # "hashtbl" ->ₛ "value_free") # Ptr |-> value_free **
    &(h # "hashtbl" ->ₛ "capacity") # UInt |-> cap **
    &(h # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks **
    PtrArray.full bucks cap ptrs **
    ht_bucket_chains_value_hole key_eq query_k idx value ptrs buckets.

Definition ht_store_node_ref_hole
    (key_eq : K -> K -> Prop) (query_k : K)
    (idx hit_slot next : Z)
    (h hash equal key_free value_free cap bucks : Z)
    (buckets : list (list (K * V))) : Assertion :=
  EX ptrs : list Z,
    “ 0 < cap /\
      0 <= idx < cap /\
      Zlength ptrs = cap /\
      Zlength buckets = cap ” &&
    &(h # "hashtbl" ->ₛ "hash") # Ptr |-> hash **
    &(h # "hashtbl" ->ₛ "equal") # Ptr |-> equal **
    &(h # "hashtbl" ->ₛ "key_free") # Ptr |-> key_free **
    &(h # "hashtbl" ->ₛ "value_free") # Ptr |-> value_free **
    &(h # "hashtbl" ->ₛ "capacity") # UInt |-> cap **
    &(h # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks **
    PtrArray.missing_i bucks idx 0 cap ptrs **
    ht_bucket_chains_except idx ptrs buckets **
    ht_chain_node_ref_hole
      key_eq query_k
      (bucks + idx * ptr_size_Z)
      hit_slot next
      (Znth idx buckets nil).

Definition ht_store_map (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (h : Z) (m : mapping K V) : Assertion :=
  “ key_eq_equiv key_eq /\ key_eq_hash_compatible key_eq key_hash ” &&
  EX hash equal key_free value_free cap bucks : Z,
  EX buckets : list (list (K * V)),
    “ buckets_abs key_eq buckets m /\ buckets_hash key_hash cap buckets /\
      buckets_unique key_eq buckets ” &&
    ht_specs key_hash key_eq hash equal key_free value_free &&
    ht_store h hash equal key_free value_free cap bucks buckets.

Definition ht_store_map_value_hole (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (h : Z) (m : mapping K V) (k : K) (value : Z) : Assertion :=
  “ key_eq_equiv key_eq /\ key_eq_hash_compatible key_eq key_hash ” &&
  EX hash equal key_free value_free cap bucks : Z,
  EX buckets : list (list (K * V)),
    “ buckets_abs key_eq buckets m /\ buckets_hash key_hash cap buckets /\
      buckets_unique key_eq buckets ” &&
    ht_specs key_hash key_eq hash equal key_free value_free &&
    ht_store_value_hole
      key_eq k
      (key_hash k mod cap) value h hash equal key_free value_free cap bucks buckets.

Definition ht_store_map_node_ref_hole
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (h : Z) (m : mapping K V) (k : K)
    (hit_slot next : Z) : Assertion :=
  “ key_eq_equiv key_eq /\ key_eq_hash_compatible key_eq key_hash ” &&
  EX hash equal key_free value_free cap bucks : Z,
  EX buckets : list (list (K * V)),
    “ buckets_abs key_eq buckets m /\ buckets_hash key_hash cap buckets /\
      buckets_unique key_eq buckets ” &&
    ht_specs key_hash key_eq hash equal key_free value_free &&
    ht_store_node_ref_hole
      key_eq k
      (key_hash k mod cap)
      hit_slot next h hash equal key_free value_free cap bucks buckets.

Lemma ht_chain_null_nil :
  ht_chain 0 nil |-- emp.
Proof.
  unfold ht_chain.
  simpl.
  Intros.
  cancel.
Qed.

Lemma ht_chain_null_nil_equiv :
  ht_chain 0 nil --||-- emp.
Proof.
  unfold ht_chain.
  simpl.
  rewrite (logic_equiv_coq_prop_andp2 (0 = 0) emp) by reflexivity.
  reflexivity.
Qed.

Lemma ht_chain_cons_ptr_nonnull
    p k v rest :
  ht_chain p ((k, v) :: rest) |--
  “ p <> 0 ” && ht_chain p ((k, v) :: rest).
Proof.
  unfold ht_chain.
  simpl.
  Intros.
  Intros key val next.
  Exists key val next.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pure_and_solve.
Qed.

Lemma ht_chain_cons
    node key val next k v rest :
  node <> 0 ->
  &(node # "ht_node" ->ₛ "key") # Ptr |-> key **
  &(node # "ht_node" ->ₛ "val") # Ptr |-> val **
  &(node # "ht_node" ->ₛ "next") # Ptr |-> next **
  storeK key k ** storeV val v ** ht_chain next rest |--
  ht_chain node ((k, v) :: rest).
Proof.
  intros Hnode; unfold ht_chain; simpl.
  Exists key val next; entailer!.
Qed.

Lemma ht_chain_nonnull_unfold
    node bucket :
  node <> 0 ->
  ht_chain node bucket |--
  EX cur_key cur_val cur_next : Z,
  EX cur_k : K, EX cur_v : V,
  EX rest_tail : list (K * V),
    “ bucket = (cur_k, cur_v) :: rest_tail ” &&
    &(node # "ht_node" ->ₛ "key") # Ptr |-> cur_key **
    &(node # "ht_node" ->ₛ "val") # Ptr |-> cur_val **
    &(node # "ht_node" ->ₛ "next") # Ptr |-> cur_next **
    storeK cur_key cur_k **
    storeV cur_val cur_v **
    ht_chain cur_next rest_tail.
Proof.
  intros Hnode.
  unfold ht_chain.
  destruct bucket as [| [cur_k cur_v] rest_tail]; simpl.
  - Intros.
    exfalso.
    lia.
  - Intros cur_key cur_val cur_next.
    Exists cur_key cur_val cur_next.
    Exists cur_k cur_v rest_tail.
    unfold ht_chain.
    entailer!.
Qed.



Lemma map_get_some_bucket_abs 
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (cap : Z) (buckets : list (list (K * V))) (m : mapping K V)
    (k : K) (v : V) :
  map_get k m (Some v) ->
  buckets_abs key_eq buckets m ->
  exists k', key_eq k k' /\
  In (k', v) (List.concat buckets).
Proof.
  intros Hget Habs.
  unfold map_get in Hget.
  unfold buckets_abs in Habs.
  generalize dependent (List.concat buckets). clear buckets. intros l.
  revert m Hget.
  induction l as [| (k', v') rest IH]; simpl in *.
  - (* l = nil *)
    intros m Hget Habs.
    unfold map_empty in Habs.
    rewrite Habs in Hget.
    discriminate.
  - (* l = (k', v') :: rest *)
    intros m Hget Habs.
    destruct Habs as [rest_map [Hrest_abs Hinsert]].
    unfold map_insert in Hinsert.
    specialize (Hinsert k).
    destruct (classic (key_eq k k')) as [Heq | Hneq].
    + (* key_eq k k' *)
      destruct Hinsert as [Hinsert _]. specialize (Hinsert Heq).
      exists k'. split; [assumption | left; f_equal].
      rewrite Hinsert in Hget. injection Hget. auto.
    + (* ~ key_eq k k' *)
      destruct Hinsert as [_ Hinsert]. specialize (Hinsert Hneq).
      rewrite Hinsert in Hget.
      apply IH with (m := rest_map) in Hget; auto.
      destruct Hget as [k'' [Heq' Hin]].
      exists k''. split; [assumption | right; assumption].
Qed.

Lemma in_concat_Znth
    {A : Type} (x : A) (buckets : list (list A)) (d : list A) :
  In x (List.concat buckets) ->
  exists idx,
    0 <= idx < Zlength buckets /\
    In x (Znth idx buckets d).
Proof.
  induction buckets as [| bucket buckets IH]; simpl; intros Hin.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exists 0. split.
      * rewrite Zlength_correct. simpl. lia.
      * rewrite Znth0_cons. exact Hin.
    + destruct (IH Hin) as [idx [Hidx Hin_idx]].
      exists (idx + 1). split.
      * rewrite Zlength_correct in *. simpl. lia.
      * rewrite Znth_cons by lia.
        replace (idx + 1 - 1) with idx by lia.
        exact Hin_idx.
Qed.

Lemma Zlength_combine_same
    {A B : Type} (l1 : list A) (l2 : list B) :
  Zlength l1 = Zlength l2 ->
  Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros Hlen.
  rewrite !Zlength_correct in *.
  apply Nat2Z.inj in Hlen.
  rewrite length_combine.
  rewrite Hlen.
  replace (Init.Nat.min (Datatypes.length l2) (Datatypes.length l2))
    with (Datatypes.length l2) by lia.
  reflexivity.
Qed.

Lemma map_get_some_bucket_abs_hash
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (cap : Z) (buckets : list (list (K * V))) (m : mapping K V)
    (k : K) (v : V) :
  key_eq_hash_compatible key_eq key_hash ->
  Zlength buckets = cap ->
  map_get k m (Some v) ->
  buckets_abs key_eq buckets m ->
  buckets_hash key_hash cap buckets ->
  exists k', key_eq k k' /\
  In (k', v) (Znth (key_hash k mod cap) buckets nil).
Proof.
  intros Hcompat Hlen Hget Habs Hhash.
  pose proof (map_get_some_bucket_abs key_eq key_hash cap buckets m k v
                Hget Habs) as [k' [Heq Hin_concat]].
  destruct (in_concat_Znth (k', v) buckets nil Hin_concat)
    as [idx [Hidx_range Hin_bucket]].
  exists k'. split; [exact Heq |].
  unfold buckets_hash in Hhash.
  assert (Hidx_hash : key_hash k' mod cap = idx).
  {
    apply (Hhash idx k' v).
    - rewrite <- Hlen. exact Hidx_range.
    - exact Hin_bucket.
  }
  unfold key_eq_hash_compatible in Hcompat.
  specialize (Hcompat k k' Heq).
  rewrite Hcompat.
  rewrite Hidx_hash.
  exact Hin_bucket.
Qed.

Lemma kvs_abs_get_first_some
    (key_eq : K -> K -> Prop)
    (pre post : list (K * V)) (hit_k query_k : K) (hit_v : V)
    (m : mapping K V) :
  (forall pk pv, In (pk, pv) pre -> ~ key_eq query_k pk) ->
  key_eq query_k hit_k ->
  kvs_abs key_eq (pre ++ (hit_k, hit_v) :: post) m ->
  map_get query_k m (Some hit_v).
Proof.
  revert m.
  induction pre as [| [pk pv] pre IH]; simpl; intros m Hpre Hhit Habs.
  - destruct Habs as [rest_map [_ Hinsert]].
    unfold map_get, map_insert in *.
    specialize (Hinsert query_k) as [Hinsert _].
    apply Hinsert; exact Hhit.
  - destruct Habs as [rest_map [Hrest_abs Hinsert]].
    assert (Hneq : ~ key_eq query_k pk).
    { apply (Hpre pk pv). left. reflexivity. }
    unfold map_insert in Hinsert.
    specialize (Hinsert query_k) as [_ Hinsert].
    unfold map_get in *.
    rewrite Hinsert by exact Hneq.
    apply (IH rest_map
              (fun pk' pv' Hin => Hpre pk' pv' (or_intror Hin))
              Hhit Hrest_abs).
Qed.

Lemma buckets_abs_get_some_at
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (cap index : Z) (buckets : list (list (K * V))) (m : mapping K V)
    (query_k hit_k : K) (hit_v : V) (pre post : list (K * V)) :
  key_eq_hash_compatible key_eq key_hash ->
  0 < cap ->
  0 <= index < cap ->
  index = key_hash query_k mod cap ->
  Zlength buckets = cap ->
  buckets_abs key_eq buckets m ->
  buckets_hash key_hash cap buckets ->
  Znth index buckets nil = pre ++ (hit_k, hit_v) :: post ->
  (forall pk pv, In (pk, pv) pre -> ~ key_eq query_k pk) ->
  key_eq query_k hit_k ->
  map_get query_k m (Some hit_v).
Proof.
  intros Hcompat Hcap Hidx Hindex Hlen Habs Hhash Hbucket Hpre Hhit.
  assert (Hidx_nat : (Z.to_nat index < List.length buckets)%nat).
  { apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct, Hlen.
    lia. }
  pose proof (list_split_nth _ (Z.to_nat index) buckets nil Hidx_nat)
    as Hsplit.
  rewrite Hsplit in Habs.
  unfold buckets_abs in Habs.
  rewrite concat_app in Habs. simpl in Habs.
  unfold Znth in Hbucket. rewrite Hbucket in Habs.
  eapply (kvs_abs_get_first_some key_eq
            (List.concat (firstn (Z.to_nat index) buckets) ++ pre)
            (post ++ List.concat
               (match buckets with
                | nil => nil
                | _ :: tail => skipn (Z.to_nat index) tail
                end))
            hit_k query_k hit_v m).
  2: exact Hhit.
  2: rewrite <- app_assoc; rewrite <- app_assoc in Habs; exact Habs.
  intros pk pv Hin.
  apply in_app_or in Hin as [Hin_prev | Hin_pre].
  - intro Heq.
    apply in_concat in Hin_prev as [bucket [Hin_bucket Hin_item]].
    destruct (In_nth _ _ nil Hin_bucket) as [n [Hn Hnth]].
    assert (Hn_lt : (n < Z.to_nat index)%nat).
    { rewrite length_firstn in Hn. lia. }
    rewrite nth_firstn in Hnth by exact Hn_lt.
    assert (Hn_range : 0 <= Z.of_nat n < cap) by lia.
    assert (Hin_Znth : In (pk, pv) (Znth (Z.of_nat n) buckets nil)).
    { unfold Znth. rewrite Nat2Z.id, Hnth. exact Hin_item. }
    pose proof (Hhash (Z.of_nat n) pk pv Hn_range Hin_Znth) as Hpk_hash.
    pose proof (Hcompat query_k pk Heq) as Hcompat_eq.
    rewrite Hindex, Hcompat_eq, Hpk_hash in Hn.
    rewrite length_firstn in Hn.
    lia.
  - exact (Hpre pk pv Hin_pre).
Qed.

Lemma kvs_abs_get_none
    (key_eq : K -> K -> Prop) items m query_k :
  (forall pk pv, In (pk, pv) items -> ~ key_eq query_k pk) ->
  kvs_abs key_eq items m ->
  map_get query_k m None.
Proof.
  revert m.
  induction items as [| [pk pv] rest IH]; simpl; intros m Hnone Habs.
  - unfold map_get, map_empty in *. apply Habs.
  - destruct Habs as [rest_map [Hrest_abs Hinsert]].
    assert (Hneq : ~ key_eq query_k pk).
    { apply (Hnone pk pv). left. reflexivity. }
    unfold map_insert in Hinsert.
    specialize (Hinsert query_k) as [_ Hinsert].
    unfold map_get in *.
    rewrite Hinsert by exact Hneq.
    apply (IH rest_map
              (fun pk' pv' Hin => Hnone pk' pv' (or_intror Hin))
              Hrest_abs).
Qed.

Lemma buckets_abs_get_none_at
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    cap buckets m index query_k pre :
  key_eq_hash_compatible key_eq key_hash ->
  0 < cap ->
  0 <= index < cap ->
  index = key_hash query_k mod cap ->
  Zlength buckets = cap ->
  buckets_abs key_eq buckets m ->
  buckets_hash key_hash cap buckets ->
  Znth index buckets nil = pre ->
  (forall pk pv, In (pk, pv) pre -> ~ key_eq query_k pk) ->
  map_get query_k m None.
Proof.
  intros Hcompat Hcap Hidx Hindex Hlen Habs Hhash Hbucket Hpre.
  unfold buckets_abs in Habs.
  eapply kvs_abs_get_none; [| exact Habs].
  intros pk pv Hin Heq.
  destruct (in_concat_Znth (pk, pv) buckets nil Hin)
    as [idx [Hidx_range Hin_idx]].
  assert (Hidx_cap : 0 <= idx < cap).
  { rewrite <- Hlen. exact Hidx_range. }
  pose proof (Hhash idx pk pv Hidx_cap Hin_idx) as Hpk_hash.
  pose proof (Hcompat query_k pk Heq) as Hcompat_eq.
  assert (Hidx_eq : idx = index).
  {
    rewrite Hindex.
    rewrite Hcompat_eq.
    symmetry.
    exact Hpk_hash.
  }
  replace (Znth idx buckets nil) with pre in Hin_idx.
  apply (Hpre pk pv Hin_idx Heq).
  rewrite Hidx_eq.
  symmetry.
  exact Hbucket.
Qed.

Lemma ht_bucket_chains_zeros_repeat_nil :
  forall cap,
    ht_bucket_chains (zeros cap) (repeat_Z nil cap) --||-- emp.
Proof.
  intros.
  unfold ht_bucket_chains, zeros, repeat_Z.
  remember (Z.to_nat cap) as n.
  clear cap Heqn.
  induction n as [| n IH]; simpl.
  - unfold iter_sepcon. simpl. reflexivity.
  - rewrite logic_equiv_iter_sepcon_cons.
    rewrite IH.
    rewrite ht_chain_null_nil_equiv.
    rewrite sepcon_emp_equiv.
    reflexivity.
Qed.

Lemma ht_bucket_chains_split_Znth
    idx ptrs buckets d :
  0 <= idx < Zlength ptrs ->
  Zlength ptrs = Zlength buckets ->
  ht_bucket_chains ptrs buckets |--
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain (Znth idx ptrs 0) (Znth idx buckets d).
Proof.
  intros Hidx Hlen.
  unfold ht_bucket_chains, ht_bucket_chains_except.
  assert (Hcombine : Zlength (combine ptrs buckets) = Zlength ptrs).
  { rewrite Zlength_combine. lia. }
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_split_remove_Znth idx
    (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets)) emp).
  2: rewrite Zlength_map, Zlength_combine; lia.
  erewrite Znth_map with (d := (0, d)); try lia.
  rewrite Znth_combine; try lia.
  entailer!.
Qed.

Lemma map_insert_exists
    (key_eq : K -> K -> Prop) (k : K) (v : V)
    (before : mapping K V) :
  exists after, map_insert key_eq k v before after.
Proof.
  unfold map_insert.
  destruct (choice
    (fun query result =>
      (key_eq query k -> result = Some v) /\
      (~ key_eq query k -> result = before query))) as [after Hafter].
  - intros query.
    destruct (classic (key_eq query k)) as [Heq | Hneq].
    + exists (Some v). split; intro; reflexivity || contradiction.
    + exists (before query). split; intro; reflexivity || contradiction.
  - exists after. exact Hafter.
Qed.

Lemma map_insert_commute_no_conflict
    (key_eq : K -> K -> Prop)
    (k pk : K) (v pv : V)
    (rest before rest_after after : mapping K V) :
  (forall query, key_eq query k -> ~ key_eq query pk) ->
  map_insert key_eq pk pv rest before ->
  map_insert key_eq k v rest rest_after ->
  map_insert key_eq k v before after ->
  map_insert key_eq pk pv rest_after after.
Proof.
  unfold map_insert.
  intros Hdisjoint Hpk Hk_rest Hk_before query.
  specialize (Hpk query) as [Hpk_eq Hpk_neq].
  specialize (Hk_rest query) as [Hk_rest_eq Hk_rest_neq].
  specialize (Hk_before query) as [Hk_before_eq Hk_before_neq].
  split.
  - intros Hquery_pk.
    assert (~ key_eq query k) as Hquery_not_k.
    {
      intro Hquery_k.
      exact (Hdisjoint query Hquery_k Hquery_pk).
    }
    rewrite Hk_before_neq by exact Hquery_not_k.
    exact (Hpk_eq Hquery_pk).
  - intros Hquery_not_pk.
    destruct (classic (key_eq query k)) as [Hquery_k | Hquery_not_k].
    + rewrite Hk_before_eq by exact Hquery_k.
      rewrite Hk_rest_eq by exact Hquery_k.
      reflexivity.
    + rewrite Hk_before_neq by exact Hquery_not_k.
      rewrite Hk_rest_neq by exact Hquery_not_k.
      exact (Hpk_neq Hquery_not_pk).
Qed.

Lemma kvs_abs_insert_after_prefix
    (key_eq : K -> K -> Prop)
    (prefix suffix : list (K * V))
    (m new_m : mapping K V) (k : K) (v : V) :
  (forall query pk pv,
      key_eq query k -> In (pk, pv) prefix -> ~ key_eq query pk) ->
  kvs_abs key_eq (prefix ++ suffix) m ->
  map_insert key_eq k v m new_m ->
  kvs_abs key_eq (prefix ++ (k, v) :: suffix) new_m.
Proof.
  revert suffix m new_m.
  induction prefix as [| [pk pv] prefix IH]; intros suffix m new_m Hdisjoint Habs Hinsert.
  - simpl in *.
    exists m. split; assumption.
  - simpl in *.
    destruct Habs as [rest_map [Hrest_abs Hpk_insert]].
    destruct (map_insert_exists key_eq k v rest_map) as [rest_after Hrest_insert].
    exists rest_after.
    split.
    + apply IH with (m := rest_map).
      * intros query pk' pv' Hquery Hin.
        apply (Hdisjoint query pk' pv' Hquery).
        right. exact Hin.
      * exact Hrest_abs.
      * exact Hrest_insert.
    + eapply map_insert_commute_no_conflict.
      * intros query Hquery.
        apply (Hdisjoint query pk pv Hquery).
        left. reflexivity.
      * exact Hpk_insert.
      * exact Hrest_insert.
      * exact Hinsert.
Qed.

Lemma map_insert_after_equiv_key
    (key_eq : K -> K -> Prop)
    (old_k k : K) (old_v v : V)
    (rest before after : mapping K V) :
  key_eq_equiv key_eq ->
  key_eq old_k k ->
  map_insert key_eq old_k old_v rest before ->
  map_insert key_eq k v before after ->
  map_insert key_eq k v rest after.
Proof.
  intros [_ _ Htrans] Hold_eq Hold_insert Hinsert.
  unfold map_insert in *.
  intros query.
  specialize (Hold_insert query) as [_ Hold_miss].
  specialize (Hinsert query) as [Hhit Hmiss].
  split.
  - exact Hhit.
  - intros Hquery_miss.
    rewrite Hmiss by exact Hquery_miss.
    apply Hold_miss.
    intros Hquery_old.
    apply Hquery_miss.
    eapply Htrans; eauto.
Qed.

Lemma kvs_abs_replace_first
    (key_eq : K -> K -> Prop)
    (prefix suffix : list (K * V))
    (m new_m : mapping K V)
    (old_k k : K) (old_v v : V) :
  key_eq_equiv key_eq ->
  (forall pk pv, In (pk, pv) prefix -> ~ key_eq pk k) ->
  key_eq old_k k ->
  kvs_abs key_eq (prefix ++ (old_k, old_v) :: suffix) m ->
  map_insert key_eq k v m new_m ->
  kvs_abs key_eq (prefix ++ (k, v) :: suffix) new_m.
Proof.
  intros Hequiv Hprefix Hold_eq.
  revert suffix m new_m.
  induction prefix as [| [pk pv] prefix IH];
    intros suffix m new_m Habs Hinsert; simpl in *.
  - destruct Habs as [rest [Hrest Hold_insert]].
    exists rest. split; [exact Hrest |].
    eapply map_insert_after_equiv_key; eauto.
  - destruct Habs as [rest_map [Hrest_abs Hpk_insert]].
    destruct (map_insert_exists key_eq k v rest_map)
      as [rest_after Hrest_insert].
    exists rest_after. split.
    + apply IH with (m := rest_map).
      * intros pk' pv' Hin.
        apply (Hprefix pk' pv'). right. exact Hin.
      * exact Hrest_abs.
      * exact Hrest_insert.
    + eapply map_insert_commute_no_conflict.
      * intros query Hquery_k Hquery_pk.
        apply (Hprefix pk pv); [left; reflexivity |].
        destruct Hequiv as [_ Hsym Htrans].
        eapply Htrans; [apply Hsym; exact Hquery_pk | exact Hquery_k].
      * exact Hpk_insert.
      * exact Hrest_insert.
      * exact Hinsert.
Qed.

Lemma concat_firstn_Znth
    {A : Type} (x : A) (idx : Z) (buckets : list (list A)) (d : list A) :
  0 <= idx <= Zlength buckets ->
  In x (List.concat (firstn (Z.to_nat idx) buckets)) ->
  exists j,
    0 <= j < idx /\ In x (Znth j buckets d).
Proof.
  intros Hidx Hin.
  destruct (in_concat_Znth x (firstn (Z.to_nat idx) buckets) d Hin)
    as [j [Hj Hin_j]].
  assert (Hj_idx : 0 <= j < idx).
  {
    rewrite Zlength_correct in Hj.
    rewrite length_firstn in Hj.
    rewrite Nat.min_l in Hj.
    - rewrite Z2Nat.id in Hj by lia.
      lia.
    - apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      lia.
  }
  exists j.
  split.
  - exact Hj_idx.
  - unfold Znth in Hin_j.
    rewrite nth_firstn with (d := d) in Hin_j.
    + exact Hin_j.
    + apply Z2Nat.inj_lt; lia.
Qed.

Lemma concat_replace_Znth
    {A : Type} (idx : Z) (buckets : list (list A)) (bucket : list A) :
  0 <= idx < Zlength buckets ->
  List.concat (replace_Znth idx bucket buckets) =
  List.concat (firstn (Z.to_nat idx) buckets) ++
    bucket ++ List.concat (skipn (S (Z.to_nat idx)) buckets).
Proof.
  intros Hidx.
  rewrite (replace_Znth_decomp idx buckets bucket) by exact Hidx.
  rewrite concat_app. simpl. reflexivity.
Qed.

(* Lemma concat_replace_Znth_cons
    idx (buckets : list (list (K * V))) (k : K) (v : V) :
  0 <= idx < Zlength buckets ->
  List.concat (replace_Znth idx ((k, v) :: Znth idx buckets nil) buckets) =
  List.concat (firstn (Z.to_nat idx) buckets) ++
    (k, v) :: (Znth idx buckets nil ++
      List.concat (skipn (S (Z.to_nat idx)) buckets)).
Proof.
  intros Hidx.
  rewrite (naive_C_Rules.IntPtrArray2.replace_Znth_decomp
             idx buckets ((k, v) :: Znth idx buckets nil)) by exact Hidx.
  rewrite concat_app. simpl.
  reflexivity.
Qed. *)

Lemma concat_decomp_Znth
    idx (buckets : list (list (K * V))) :
  0 <= idx < Zlength buckets ->
  List.concat buckets =
  List.concat (firstn (Z.to_nat idx) buckets) ++
    Znth idx buckets nil ++
    List.concat (skipn (S (Z.to_nat idx)) buckets).
Proof.
  intros Hidx.
  rewrite (firstn_skipSn nil (Z.to_nat idx) buckets) at 1.
  - rewrite concat_app. simpl. reflexivity.
  - rewrite Zlength_correct in Hidx.
    lia.
Qed.

Lemma buckets_hash_replace_Znth
    (key_hash : K -> Z) (cap idx : Z)
    (buckets : list (list (K * V))) (bucket : list (K * V)) :
  Zlength buckets = cap ->
  0 <= idx < cap ->
  buckets_hash key_hash cap buckets ->
  (forall k v, In (k, v) bucket -> key_hash k mod cap = idx) ->
  buckets_hash key_hash cap (replace_Znth idx bucket buckets).
Proof.
  intros Hlen Hidx Hhash Hbucket.
  unfold buckets_hash in *.
  intros j k v Hj Hin.
  destruct (Z.eq_dec j idx) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same in Hin by lia.
    exact (Hbucket k v Hin).
  - rewrite Znth_replace_Znth_Diff in Hin by lia.
    exact (Hhash j k v Hj Hin).
Qed.

Lemma buckets_hash_replace_entry
    (key_hash : K -> Z) (cap idx : Z)
    (buckets : list (list (K * V)))
    (prefix suffix : list (K * V)) (old_entry : K * V)
    (k : K) (v : V) :
  Zlength buckets = cap ->
  0 <= idx < cap ->
  idx = key_hash k mod cap ->
  buckets_hash key_hash cap buckets ->
  Znth idx buckets nil = prefix ++ old_entry :: suffix ->
  buckets_hash key_hash cap
    (replace_Znth idx (prefix ++ (k, v) :: suffix) buckets).
Proof.
  intros Hlen Hidx Hnew_hash Hhash Hbucket.
  eapply buckets_hash_replace_Znth; eauto.
  intros key value Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - apply (Hhash idx key value Hidx).
    rewrite Hbucket. apply in_or_app. left. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hin | Hin].
    + injection Hin as Hkey Hvalue. subst key value. symmetry. exact Hnew_hash.
    + apply (Hhash idx key value Hidx).
      rewrite Hbucket. apply in_or_app. right. simpl. right. exact Hin.
Qed.

Lemma buckets_abs_replace_first_in_bucket
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (cap idx : Z) (buckets : list (list (K * V)))
    (prefix suffix : list (K * V))
    (m new_m : mapping K V) (old_k k : K) (old_v v : V) :
  key_eq_equiv key_eq ->
  key_eq_hash_compatible key_eq key_hash ->
  0 < cap ->
  Zlength buckets = cap ->
  idx = key_hash k mod cap ->
  buckets_hash key_hash cap buckets ->
  Znth idx buckets nil = prefix ++ (old_k, old_v) :: suffix ->
  (forall pk pv, In (pk, pv) prefix -> ~ key_eq pk k) ->
  key_eq old_k k ->
  buckets_abs key_eq buckets m ->
  map_insert key_eq k v m new_m ->
  buckets_abs key_eq
    (replace_Znth idx (prefix ++ (k, v) :: suffix) buckets) new_m.
Proof.
  intros Hequiv Hcompatible Hcap Hlen Hidx Hhash Hbucket
    Hprefix Hold_eq Habs Hinsert.
  assert (Hidx_range : 0 <= idx < Zlength buckets) by
    (rewrite Hlen, Hidx; apply Z.mod_pos_bound; exact Hcap).
  unfold buckets_abs in Habs |- *.
  rewrite concat_replace_Znth by exact Hidx_range.
  rewrite (concat_decomp_Znth idx buckets Hidx_range) in Habs.
  rewrite Hbucket in Habs.
  rewrite <- !app_assoc in Habs |- *.
  rewrite <- app_comm_cons in Habs |- *.
  rewrite !app_assoc in Habs |- *.
  eapply kvs_abs_replace_first; eauto.
  intros pk pv Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - destruct (concat_firstn_Znth
      (pk, pv) idx buckets nil ltac:(lia) Hin) as [j [Hj Hinj]].
    intros Hpk.
    unfold buckets_hash in Hhash.
    specialize (Hhash j pk pv ltac:(lia) Hinj).
    rewrite (Hcompatible pk k Hpk), <- Hidx in Hhash.
    lia.
  - exact (Hprefix pk pv Hin).
Qed.

Definition ht_buckets_insert (idx : Z) (k : K) (v : V) buckets :=
  replace_Znth idx ((k, v) :: Znth idx buckets nil) buckets.

(* Lemma buckets_abs_insert_bucket_head
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    (cap : Z) (buckets : list (list (K * V))) (m : mapping K V)
    (k : K) (v : V) :
  Zlength buckets = cap ->
  key_eq_hash_compatible key_eq key_hash ->
  buckets_abs key_eq buckets m ->
  buckets_hash key_hash cap buckets ->
  exists new_m,
    map_insert key_eq k v m new_m /\
    buckets_abs key_eq
      (ht_buckets_insert (key_hash k mod cap) k v buckets)
      new_m.
Proof.
  intros Hbuckets_len Hcompat Habs Hhash.
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  exists new_m.
  split; [exact Hinsert |].
  unfold buckets_abs in *.
  rewrite concat_replace_Znth_cons by lia.
  rewrite (concat_decomp_Znth (key_hash k mod cap) buckets) in Habs by lia.
  apply kvs_abs_insert_after_prefix with (m := m).
  - intros query pk pv Hquery_k Hin_prefix Hquery_pk.
    destruct (concat_firstn_Znth (pk, pv) idx buckets nil ltac:(lia) Hin_prefix)
      as [j [Hj Hin_j]].
    unfold buckets_hash in Hhash.
    pose proof (Hhash j pk pv ltac:(lia) Hin_j) as Hpk_hash.
    unfold key_eq_hash_compatible in Hcompat.
    pose proof (Hcompat query k Hquery_k) as Hquery_k_hash.
    pose proof (Hcompat query pk Hquery_pk) as Hquery_pk_hash.
    assert (key_hash pk = key_hash k) by lia.
    rewrite H in Hpk_hash.
    rewrite <- Hidx_hash in Hpk_hash.
    lia.
  - exact Habs.
  - exact Hinsert.
Qed. *)

Lemma combine_replace_Znth_both
    {A B : Type} idx (l1 : list A) (l2 : list B) a b :
  0 <= idx < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  combine (replace_Znth idx a l1) (replace_Znth idx b l2) =
  replace_Znth idx (a, b) (combine l1 l2).
Proof.
  intros Hidx Hlen.
  apply (proj2 (list_eq_ext _ _ (a, b))).
  split.
  - replace (Zlength (combine (replace_Znth idx a l1) (replace_Znth idx b l2)))
      with (Zlength l1).
    + rewrite Zlength_replace_Znth.
      rewrite Zlength_combine_same by lia.
      reflexivity.
    + rewrite Zlength_combine_same.
      * rewrite Zlength_replace_Znth.
        reflexivity.
      * rewrite !Zlength_replace_Znth.
        exact Hlen.
  - intros i Hi.
    assert (Hreplace_len :
      Zlength (replace_Znth idx a l1) =
      Zlength (replace_Znth idx b l2)).
    {
      rewrite !Zlength_replace_Znth.
      exact Hlen.
    }
    assert (Hi_l1 : 0 <= i < Zlength l1).
    {
      replace (Zlength l1) with
        (Zlength (combine (replace_Znth idx a l1) (replace_Znth idx b l2))).
      - exact Hi.
      - rewrite Zlength_combine_same by exact Hreplace_len.
        rewrite Zlength_replace_Znth.
        reflexivity.
    }
    destruct (Z.eq_dec i idx) as [Hi_eq | Hi_neq].
    + subst i.
      rewrite Znth_combine by
        (rewrite ?Zlength_replace_Znth; lia).
      rewrite !Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same.
      * reflexivity.
      * rewrite Zlength_combine_same by lia.
        lia.
    + rewrite Znth_replace_Znth_Diff.
      * rewrite Znth_combine by
          (rewrite ?Zlength_replace_Znth; lia).
        rewrite !Znth_replace_Znth_Diff by lia.
        rewrite Znth_combine by lia.
        reflexivity.
      * rewrite Zlength_combine_same by lia.
        lia.
      * rewrite Zlength_combine_same by lia.
        exact Hi_l1.
      * lia.
Qed.

(* The statement/proof of this helper is under review; do not use it for now.
*)

Lemma ht_bucket_chains_merge_remove_Znth
    idx ptrs buckets :
  0 <= idx < Zlength ptrs ->
  Zlength ptrs = Zlength buckets ->
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain (Znth idx ptrs 0) (Znth idx buckets nil) |--
  ht_bucket_chains ptrs buckets.
Proof.
  intros Hidx Hlen.
  unfold ht_bucket_chains, ht_bucket_chains_except.
  simpl.
  rewrite derivable1_sepcon_comm.
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_merge_remove_Znth idx
    (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets))).
  2: rewrite Zlength_map, Zlength_combine; lia.
  set (l := map _ (combine _ _)).
  replace (ht_chain (Znth idx ptrs 0) (Znth idx buckets nil)) with
    (Znth idx l (ht_chain 0 nil)).
  2: {
    subst l.
    rewrite Znth_map with (d := (0, nil)).
    2: rewrite Zlength_combine; lia.
    rewrite Znth_combine; try lia.
    reflexivity.
  }
  rewrite replace_Znth_Znth.
  reflexivity.
Qed.

Lemma ht_bucket_chains_merge_remove_Znth_replace
    idx ptrs buckets head :
  0 <= idx < Zlength ptrs ->
  Zlength ptrs = Zlength buckets ->
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain head (Znth idx buckets nil) |--
  ht_bucket_chains (replace_Znth idx head ptrs) buckets.
Proof.
  intros Hidx Hlen.
  unfold ht_bucket_chains, ht_bucket_chains_except.
  simpl.
  rewrite derivable1_sepcon_comm.
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_merge_remove_Znth idx
    (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets))).
  2: rewrite Zlength_map, Zlength_combine; lia.
  replace
    (replace_Znth idx (ht_chain head (Znth idx buckets nil))
       (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets)))
    with
    (map (fun '(p, bucket) => ht_chain p bucket)
       (combine (replace_Znth idx head ptrs) buckets)).
  - reflexivity.
  - change (ht_chain head (Znth idx buckets nil))
      with ((fun '(p, bucket) => ht_chain p bucket)
              (head, Znth idx buckets nil)).
    rewrite <- map_replace_Znth.
    rewrite replace_Znth_combine_l with (d2 := nil).
    reflexivity.
Qed.

Lemma ht_bucket_chains_merge_replace_Znth
    idx ptrs buckets head bucket :
  0 <= idx < Zlength ptrs ->
  Zlength ptrs = Zlength buckets ->
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain head bucket |--
  ht_bucket_chains
    (replace_Znth idx head ptrs)
    (replace_Znth idx bucket buckets).
Proof.
  intros Hidx Hlen.
  unfold ht_bucket_chains, ht_bucket_chains_except.
  simpl.
  rewrite derivable1_sepcon_comm.
  rewrite map_remove_Znth.
  sep_apply (iter_sepcon_merge_remove_Znth idx
    (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets))).
  2: rewrite Zlength_map, Zlength_combine; lia.
  replace
    (replace_Znth idx (ht_chain head bucket)
       (map (fun '(p, bucket) => ht_chain p bucket) (combine ptrs buckets)))
    with
    (map (fun '(p, bucket) => ht_chain p bucket)
       (combine (replace_Znth idx head ptrs)
          (replace_Znth idx bucket buckets))).
  - reflexivity.
  - change (ht_chain head bucket)
      with ((fun '(p, bucket) => ht_chain p bucket) (head, bucket)).
    rewrite <- map_replace_Znth.
    rewrite combine_replace_Znth_both; reflexivity || lia.
Qed.

Lemma ht_chain_find_some
    (key_eq : K -> K -> Prop) (query_k : K)
    (p : addr) (bucket : list (K * V))
    (k : K) (v : V) :
  key_eq query_k k ->
  In (k, v) bucket ->
  ht_chain p bucket |--
  EX value : addr,
  ht_chain_value_hole key_eq query_k p value bucket ** storeV value v.
Proof.
  intros Hkey_eq.
  unfold ht_chain.
  revert p.
  induction bucket as [| [head_k head_v] rest IH]; simpl; intros p Hin.
  - contradiction.
  - Intros key value next.
    destruct Hin as [Hhit | Hin].
    + injection Hhit as Hk Hv. subst head_k head_v.
      unfold ht_chain_value_hole, ht_chain.
      Exists value.
      Exists ( @nil (K * V)).
      Exists k v rest.
      Exists p key next.
      simpl.
      entailer!.
    + sep_apply (IH next Hin).
      Intros hit_value.
      Exists hit_value.
      unfold ht_chain_value_hole.
      Intros pre hit_k old_v.
      Intros post hit_node hit_key hit_next.
      Exists ((head_k, head_v) :: pre).
      Exists hit_k old_v post.
      Exists hit_node hit_key hit_next.
      destruct H0 as [Hbucket [Hhit_key_eq Hhit_nonnull]].
      simpl. fold ht_chain_seg.
      Exists key value next.
      entailer!.
      rewrite Hbucket. reflexivity.
Qed.

Lemma ht_chain_seg_snoc
    p cur cur_next cur_key cur_val
    (cur_k : K) (cur_v : V) pre :
  cur <> 0 ->
  ht_chain_seg p cur pre **
  &(cur # "ht_node" ->ₛ "key") # Ptr |-> cur_key **
  &(cur # "ht_node" ->ₛ "val") # Ptr |-> cur_val **
  &(cur # "ht_node" ->ₛ "next") # Ptr |-> cur_next **
  storeK cur_key cur_k **
  storeV cur_val cur_v |--
  ht_chain_seg p cur_next (pre ++ (cur_k, cur_v) :: nil).
Proof.
  intros Hcur.
  revert p.
  induction pre as [| [head_k head_v] rest IH]; intros p; simpl.
  - Intros.
    Exists cur_key cur_val cur_next.
    subst.
    entailer!.
  - Intros key val next.
    sep_apply (IH next).
    Exists key val next.
    entailer!.
Qed.

Lemma ht_chain_null_inv bucket :
  ht_chain 0 bucket |-- “ bucket = nil ” && emp.
Proof.
  unfold ht_chain.
  destruct bucket as [| [k v] rest]; simpl.
  - entailer!.
  - Intros key val next.
    exfalso.
    lia.
Qed.

Lemma ht_chain_seg_app p q r l1 l2 :
  ht_chain_seg p q l1 **
  ht_chain_seg q r l2 |--
  ht_chain_seg p r (l1 ++ l2).
Proof.
  revert p.
  induction l1 as [| [k v] rest IH]; intros p; simpl.
  - Intros.
    subst p.
    cancel.
  - Intros key val next.
    sep_apply (IH next).
    Exists key val next.
    entailer!.
Qed.

Lemma ht_chain_seg_hit_value_hole
    (key_eq : K -> K -> Prop) query_k
    p hit_node hit_key hit_val hit_next
    hit_k hit_v pre post :
  key_eq query_k hit_k ->
  hit_node <> 0 ->
  ht_chain_seg p hit_node pre **
  &(hit_node # "ht_node" ->ₛ "key") # Ptr |-> hit_key **
  &(hit_node # "ht_node" ->ₛ "val") # Ptr |-> hit_val **
  &(hit_node # "ht_node" ->ₛ "next") # Ptr |-> hit_next **
  storeK hit_key hit_k **
  ht_chain hit_next post |--
  ht_chain_value_hole key_eq query_k p hit_val
    (pre ++ (hit_k, hit_v) :: post).
Proof.
  intros Hkey_eq Hhit_node.
  unfold ht_chain_value_hole.
  Exists pre hit_k hit_v post.
  Exists hit_node hit_key hit_next.
  entailer!.
Qed.

Lemma ht_chain_bseg_len1
    slot node key val (k : K) (v : V) :
  node <> 0 ->
  slot # Ptr |-> node **
  &(node # "ht_node" ->ₛ "key") # Ptr |-> key **
  &(node # "ht_node" ->ₛ "val") # Ptr |-> val **
  storeK key k **
  storeV val v |--
  ht_chain_bseg slot (&(node # "ht_node" ->ₛ "next")) ((k, v) :: nil).
Proof.
  intros Hnode.
  simpl.
  Exists node key val.
  entailer!.
Qed.

Lemma ht_chain_bseg_app
    start mid finish l1 l2 :
  ht_chain_bseg start mid l1 **
  ht_chain_bseg mid finish l2 |--
  ht_chain_bseg start finish (l1 ++ l2).
Proof.
  revert start.
  induction l1 as [| [k v] rest IH]; simpl; intros start.
  - entailer!.
    subst start.
    entailer!.
  - Intros node key val.
    Exists node key val.
    entailer!.
Qed.

Lemma ht_chain_bseg_snoc
    start slot node key val (k : K) (v : V) pre :
  node <> 0 ->
  ht_chain_bseg start slot pre **
  slot # Ptr |-> node **
  &(node # "ht_node" ->ₛ "key") # Ptr |-> key **
  &(node # "ht_node" ->ₛ "val") # Ptr |-> val **
  storeK key k **
  storeV val v |--
  ht_chain_bseg start (&(node # "ht_node" ->ₛ "next"))
    (pre ++ (k, v) :: nil).
Proof.
  intros Hnode.
  sep_apply (ht_chain_bseg_len1 slot node key val k v).
  - sep_apply (ht_chain_bseg_app start slot
      (&(node # "ht_node" ->ₛ "next")) pre ((k, v) :: nil)).
    cancel.
  - exact Hnode.
Qed.

Lemma ht_chain_bseg_snoc_keep_next
    start slot node key val next (k : K) (v : V) pre :
  node <> 0 ->
  ht_chain_bseg start slot pre **
  slot # Ptr |-> node **
  &(node # "ht_node" ->ₛ "key") # Ptr |-> key **
  &(node # "ht_node" ->ₛ "val") # Ptr |-> val **
  &(node # "ht_node" ->ₛ "next") # Ptr |-> next **
  storeK key k **
  storeV val v |--
  &(node # "ht_node" ->ₛ "next") # Ptr |-> next **
  ht_chain_bseg start (&(node # "ht_node" ->ₛ "next"))
    (pre ++ (k, v) :: nil).
Proof.
  intros Hnode.
  revert start.
  induction pre as [| [head_k head_v] rest IH]; simpl; intros start.
  - Intros.
    subst start.
    Exists node key val.
    entailer!.
  - Intros head_node head_key head_val.
    Exists head_node head_key head_val.
    sep_apply (IH (&(head_node # "ht_node" ->ₛ "next"))).
    entailer!.
Qed.

Lemma ht_chain_bseg_2_chain_seg
    start_slot end_slot end_node pre :
  ht_chain_bseg start_slot end_slot pre **
  end_slot # Ptr |-> end_node |--
  EX head : Z,
    start_slot # Ptr |-> head **
    ht_chain_seg head end_node pre.
Proof.
  revert start_slot.
  induction pre as [| [k v] rest IH]; simpl; intros start_slot.
  - Intros.
    subst start_slot.
    Exists end_node.
    entailer!.
  - Intros node key val.
    Exists node.
    sep_apply (IH (&(node # "ht_node" ->ₛ "next"))).
    Intros next.
    Exists key val next.
    entailer!.
Qed.

Lemma ht_chain_bseg_2_chain
    start_slot end_slot end_node pre post :
  ht_chain_bseg start_slot end_slot pre **
  end_slot # Ptr |-> end_node **
  ht_chain end_node post |--
  EX head : Z,
    start_slot # Ptr |-> head **
    ht_chain head (pre ++ post).
Proof.
  intros.
  sep_apply ht_chain_bseg_2_chain_seg.
  Intros head.
  Exists head.
  unfold ht_chain.
  sep_apply ht_chain_seg_app.
  entailer!.
Qed.

Lemma ht_bucket_chains_bseg_merge
    idx cap bucks ptrs buckets slot node pre post :
  0 <= idx < cap ->
  Zlength ptrs = cap ->
  Zlength buckets = cap ->
  PtrArray.missing_i bucks idx 0 cap ptrs **
  ht_bucket_chains_except idx ptrs buckets **
  ht_chain_bseg (bucks + idx * sizeof(PTR)) slot pre **
  slot # Ptr |-> node ** ht_chain node post |--
  EX head,
    PtrArray.full bucks cap (replace_Znth idx head ptrs) **
    ht_bucket_chains
      (replace_Znth idx head ptrs)
      (replace_Znth idx (pre ++ post) buckets).
Proof.
  intros Hidx Hptrs Hbuckets.
  sep_apply (ht_chain_bseg_2_chain
    (bucks + idx * sizeof(PTR)) slot node pre post).
  Intros head; Exists head.
  change (sizeof(PTR)) with ptr_size_Z.
  sep_apply (PtrArray.missing_i_merge_to_full bucks idx cap head ptrs).
  sep_apply (ht_bucket_chains_merge_replace_Znth
    idx ptrs buckets head (pre ++ post)).
  all: entailer!; try lia.
Qed.

Lemma kvs_abs_remove
    (key_eq : K -> K -> Prop) pre post m k hit_k hit_v :
  key_eq_equiv key_eq ->
  (forall pk pv, In (pk, pv) pre -> ~ key_eq k pk) ->
  key_eq k hit_k ->
  kvs_unique key_eq (pre ++ (hit_k, hit_v) :: post) ->
  kvs_abs key_eq (pre ++ (hit_k, hit_v) :: post) m ->
  exists new_m,
    map_remove key_eq k m new_m /\
    kvs_abs key_eq (pre ++ post) new_m /\
    kvs_unique key_eq (pre ++ post).
Proof.
  intros Hequiv Hpre Hhit Huniq Habs.
  destruct Hequiv as [Href Hsym Htrans].
  revert post m Hpre Huniq Habs.
  induction pre as [| [pk pv] pre IH];
    intros post m Hpre Huniq Habs; simpl in *.
  - destruct Huniq as [Hnone Huniq].
    destruct Habs as [rest_m [Hrest Hinsert]].
    exists rest_m; split; [| split; assumption].
    unfold map_remove; intros query; split.
    + intros Hq; eapply kvs_abs_get_none; [| exact Hrest].
      intros pk' pv' Hin Heq; apply (Hnone pk' pv' Hin).
      eapply Htrans; [apply Hsym; exact Hhit |].
      eapply Htrans; [apply Hsym; exact Hq | exact Heq].
    + intros Hq; unfold map_insert in Hinsert.
      specialize (Hinsert query) as [_ Hmiss].
      symmetry; apply Hmiss; intro Hqh; apply Hq.
      eapply Htrans; [exact Hqh | apply Hsym; exact Hhit].
  - destruct Huniq as [Hpk_none Huniq].
    destruct Habs as [rest_m [Hrest Hpk_insert]].
    assert (Hkpk : ~ key_eq k pk) by
      (apply (Hpre pk pv); left; reflexivity).
    destruct (IH post rest_m
      (fun pk' pv' Hin => Hpre pk' pv' (or_intror Hin)) Huniq Hrest)
      as [new_rest [Hremove [Hnew_abs Hnew_unique]]].
    destruct (map_insert_exists key_eq pk pv new_rest)
      as [new_m Hnew_insert].
    exists new_m; split.
    + unfold map_remove in Hremove |- *.
      unfold map_insert in Hpk_insert, Hnew_insert.
      intros query.
      specialize (Hremove query) as [Hremove_hit Hremove_miss].
      specialize (Hpk_insert query) as [Hold_hit Hold_miss].
      specialize (Hnew_insert query) as [Hnew_hit Hnew_miss].
      split.
      * intros Hq; rewrite Hnew_miss.
        -- apply Hremove_hit; exact Hq.
        -- intro Hqp; apply Hkpk.
           eapply Htrans; [apply Hsym; exact Hq | exact Hqp].
      * intros Hq.
        destruct (classic (key_eq query pk)) as [Hqp | Hqp].
        -- rewrite Hnew_hit by exact Hqp.
           rewrite Hold_hit by exact Hqp; reflexivity.
        -- rewrite Hnew_miss by exact Hqp.
           rewrite Hold_miss by exact Hqp.
           apply Hremove_miss; exact Hq.
    + split.
      * exists new_rest; split; assumption.
      * simpl; split; [| exact Hnew_unique].
        intros k' v' Hin; apply (Hpk_none k' v').
        apply in_app_or in Hin; apply in_or_app.
        destruct Hin as [Hin | Hin].
        -- left; exact Hin.
        -- right; simpl; right; exact Hin.
Qed.

Lemma buckets_remove_first_in_bucket
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    cap idx (buckets : list (list (K * V))) pre post
    (m : mapping K V) k hit_k hit_v :
  key_eq_equiv key_eq ->
  key_eq_hash_compatible key_eq key_hash ->
  0 < cap ->
  Zlength buckets = cap ->
  idx = key_hash k mod cap ->
  buckets_hash key_hash cap buckets ->
  Znth idx buckets nil = pre ++ (hit_k, hit_v) :: post ->
  (forall pk pv, In (pk, pv) pre -> ~ key_eq k pk) ->
  key_eq k hit_k ->
  buckets_abs key_eq buckets m ->
  buckets_unique key_eq buckets ->
  exists new_m,
    map_remove key_eq k m new_m /\
    buckets_abs key_eq
      (replace_Znth idx (pre ++ post) buckets) new_m /\
    buckets_hash key_hash cap
      (replace_Znth idx (pre ++ post) buckets) /\
    buckets_unique key_eq (replace_Znth idx (pre ++ post) buckets).
Proof.
  intros Hequiv Hcompat Hcap Hlen Hidx Hhash Hbucket Hpre Hhit Habs Huniq.
  assert (Hidx_range : 0 <= idx < Zlength buckets) by
    (rewrite Hlen, Hidx; apply Z.mod_pos_bound; exact Hcap).
  unfold buckets_abs in Habs |- *.
  unfold buckets_unique in Huniq |- *.
  rewrite !concat_replace_Znth by exact Hidx_range.
  rewrite (concat_decomp_Znth idx buckets Hidx_range) in Habs, Huniq.
  rewrite Hbucket in Habs, Huniq.
  rewrite <- !app_assoc in Habs, Huniq |- *.
  rewrite <- app_comm_cons in Habs, Huniq.
  rewrite !app_assoc in Habs, Huniq |- *.
  assert (Hglobal : forall pk pv,
    In (pk, pv) (List.concat (firstn (Z.to_nat idx) buckets) ++ pre) ->
    ~ key_eq k pk).
  { intros pk pv Hin; apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; [| exact (Hpre pk pv Hin)].
    destruct (concat_firstn_Znth (pk, pv) idx buckets nil ltac:(lia) Hin)
      as [j [Hj Hinj]].
    intro Hkp.
    pose proof (Hhash j pk pv ltac:(lia) Hinj) as Hpk_hash.
    pose proof (Hcompat k pk Hkp) as Hcompat_eq.
    rewrite <- Hcompat_eq, <- Hidx in Hpk_hash; lia. }
  destruct (kvs_abs_remove key_eq
    (List.concat (firstn (Z.to_nat idx) buckets) ++ pre)
    (post ++ List.concat (skipn (S (Z.to_nat idx)) buckets))
    m k hit_k hit_v Hequiv Hglobal Hhit Huniq Habs)
    as [new_m [Hremove [Hnew_abs Hnew_unique]]].
  exists new_m; repeat split; try assumption.
  - exact (proj1 (Hremove query)).
  - exact (proj2 (Hremove query)).
  - eapply buckets_hash_replace_Znth; eauto.
    + lia.
    + intros key value Hin; apply (Hhash idx key value); [lia |].
      rewrite Hbucket; apply in_or_app.
      apply in_app_or in Hin; destruct Hin as [Hin | Hin].
      * left; exact Hin.
      * right; simpl; right; exact Hin.
Qed.

Lemma kvs_unique_insert
    (key_eq : K -> K -> Prop) pre post k v :
  key_eq_equiv key_eq ->
  (forall pk pv, In (pk, pv) (pre ++ post) -> ~ key_eq pk k) ->
  kvs_unique key_eq (pre ++ post) ->
  kvs_unique key_eq (pre ++ (k, v) :: post).
Proof.
  intros [_ Hsym _].
  revert post.
  induction pre as [| [pk pv] pre IH]; intros post Hnone Huniq; simpl in *.
  - split; [| exact Huniq].
    intros k' v' Hin Hkk'.
    apply (Hnone k' v' Hin), Hsym, Hkk'.
  - destruct Huniq as [Hhead Htail]; split.
    + intros k' v' Hin.
      apply in_app_or in Hin; destruct Hin as [Hin | [Heq | Hin]].
      * apply (Hhead k' v'), in_or_app; left; exact Hin.
      * injection Heq; intros; subst; apply (Hnone pk pv); left; reflexivity.
      * apply (Hhead k' v'), in_or_app; right; exact Hin.
    + apply IH.
      * intros k' v' Hin; apply (Hnone k' v'); right; exact Hin.
      * exact Htail.
Qed.

Lemma buckets_insert_new_head
    (key_eq : K -> K -> Prop) (key_hash : K -> Z)
    cap idx (buckets : list (list (K * V))) bucket
    (m : mapping K V) k v :
  key_eq_equiv key_eq ->
  key_eq_hash_compatible key_eq key_hash ->
  0 < cap ->
  Zlength buckets = cap ->
  idx = key_hash k mod cap ->
  buckets_hash key_hash cap buckets ->
  Znth idx buckets nil = bucket ->
  (forall pk pv, In (pk, pv) bucket -> ~ key_eq pk k) ->
  buckets_abs key_eq buckets m ->
  buckets_unique key_eq buckets ->
  exists new_m,
    map_insert key_eq k v m new_m /\
    buckets_abs key_eq
      (replace_Znth idx ((k, v) :: bucket) buckets) new_m /\
    buckets_hash key_hash cap
      (replace_Znth idx ((k, v) :: bucket) buckets) /\
    buckets_unique key_eq
      (replace_Znth idx ((k, v) :: bucket) buckets).
Proof.
  intros Hequiv Hcompat Hcap Hlen Hidx Hhash Hbucket Hnone Habs Huniq.
  assert (Hidx_range : 0 <= idx < Zlength buckets) by
    (rewrite Hlen, Hidx; apply Z.mod_pos_bound; exact Hcap).
  set (before := List.concat (firstn (Z.to_nat idx) buckets)).
  set (after := List.concat (skipn (S (Z.to_nat idx)) buckets)).
  assert (Hflat : List.concat buckets = before ++ bucket ++ after).
  { subst before after.
    rewrite (concat_decomp_Znth idx buckets Hidx_range).
    rewrite Hbucket; reflexivity. }
  assert (Hflat_none : forall pk pv,
      In (pk, pv) (before ++ bucket ++ after) -> ~ key_eq pk k).
  { intros pk pv Hin Hpk.
    destruct (in_concat_Znth (pk, pv) buckets nil)
      as [j [Hj Hinj]].
    - rewrite Hflat; exact Hin.
    - pose proof (Hhash j pk pv ltac:(rewrite <- Hlen; exact Hj) Hinj)
        as Hpk_hash.
      pose proof (Hcompat pk k Hpk) as Hhash_eq.
      rewrite Hhash_eq, <- Hidx in Hpk_hash.
      subst j; rewrite Hbucket in Hinj.
      exact (Hnone pk pv Hinj Hpk). }
  destruct (map_insert_exists key_eq k v m) as [new_m Hinsert].
  exists new_m; split; [exact Hinsert |]; repeat split.
  - unfold buckets_abs in Habs |- *.
    rewrite concat_replace_Znth by exact Hidx_range.
    rewrite Hflat in Habs.
    change (kvs_abs key_eq (before ++ (k, v) :: bucket ++ after) new_m).
    eapply kvs_abs_insert_after_prefix; eauto.
    intros query pk pv Hquery Hin Hquery_pk.
    apply (Hflat_none pk pv); [|].
    + apply in_or_app; left; exact Hin.
    + destruct Hequiv as [_ Hsym Htrans].
      eapply Htrans; [apply Hsym; exact Hquery_pk | exact Hquery].
  - eapply buckets_hash_replace_Znth.
    + exact Hlen.
    + rewrite Hidx; apply Z.mod_pos_bound; lia.
    + exact Hhash.
    + intros pk pv [Heq | Hin].
      * injection Heq; intros; subst pk pv; symmetry; exact Hidx.
      * apply (Hhash idx pk pv); [rewrite Hidx; apply Z.mod_pos_bound; lia |].
        rewrite Hbucket; exact Hin.
  - unfold buckets_unique in Huniq |- *.
    rewrite concat_replace_Znth by exact Hidx_range.
    rewrite Hflat in Huniq.
    change (kvs_unique key_eq (before ++ (k, v) :: bucket ++ after)).
    eapply kvs_unique_insert; eauto.
Qed.

Lemma kvs_unique_replace_equiv
    (key_eq : K -> K -> Prop) pre post old_k old_v k v :
  key_eq_equiv key_eq ->
  key_eq old_k k ->
  kvs_unique key_eq (pre ++ (old_k, old_v) :: post) ->
  kvs_unique key_eq (pre ++ (k, v) :: post).
Proof.
  intros Hequiv Hold Huniq.
  destruct Hequiv as [Href Hsym Htrans].
  induction pre as [| [pk pv] pre IH]; simpl in *.
  - destruct Huniq as [Hnone Huniq]; split; [| exact Huniq].
    intros k' v' Hin Hkk'; apply (Hnone k' v' Hin).
    eapply Htrans; [exact Hold | exact Hkk'].
  - destruct Huniq as [Hnone Huniq]; split; [| apply IH; exact Huniq].
    intros k' v' Hin; apply in_app_or in Hin.
    destruct Hin as [Hin | [Heq | Hin]].
    + apply (Hnone k' v'); apply in_or_app; left; exact Hin.
    + injection Heq; intros; subst; intro Hpk.
      apply (Hnone old_k old_v).
      * apply in_or_app; right; left; reflexivity.
      * eapply Htrans; [exact Hpk | apply Hsym; exact Hold].
    + apply (Hnone k' v'); apply in_or_app; right; simpl; right; exact Hin.
Qed.

Lemma buckets_unique_replace_entry
    (key_eq : K -> K -> Prop) idx buckets pre post old_k old_v k v :
  key_eq_equiv key_eq ->
  0 <= idx < Zlength buckets ->
  Znth idx buckets nil = pre ++ (old_k, old_v) :: post ->
  key_eq old_k k ->
  buckets_unique key_eq buckets ->
  buckets_unique key_eq
    (replace_Znth idx (pre ++ (k, v) :: post) buckets).
Proof.
  intros Hequiv Hidx Hbucket Hold Huniq.
  unfold buckets_unique in Huniq |- *.
  rewrite concat_replace_Znth by exact Hidx.
  rewrite (concat_decomp_Znth idx buckets Hidx) in Huniq.
  rewrite Hbucket in Huniq.
  rewrite <- !app_assoc in Huniq |- *.
  rewrite <- app_comm_cons in Huniq |- *.
  rewrite !app_assoc in Huniq |- *.
  eapply kvs_unique_replace_equiv; eauto.
Qed.

End HashTable.
