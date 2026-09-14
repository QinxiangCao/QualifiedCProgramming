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
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.

Lemma proof_of_hashtbl_add_entail_wit_1_split_goal_1 : hashtbl_add_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (proj2 (Z.rem_bound_pos retval 211 PreH1 ltac:(lia))).
Qed.

Lemma proof_of_hashtbl_add_entail_wit_1_split_goal_2 : hashtbl_add_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.rem_nonneg; lia.
Qed.

Lemma proof_of_hashtbl_add_entail_wit_1 : hashtbl_add_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_hashtbl_add_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_hashtbl_add_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_hashtbl_add_return_wit_1 : hashtbl_add_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (PtrArray.full_Zlength bucks_ph 211
      (replace_Znth (retval % 211) retval_2 lh)).
  Intros_p Hlen_replaced.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite Zlength_replace_Znth in Hlen_replaced.
    exact Hlen_replaced. }
  assert (Hidx_lh : 0 <= retval % 211 < Zlength lh) by lia.
  assert (Hnode_none : m_node k = None).
  { eapply node_value_map_none__add_final; eauto. }
  assert (Hnode_new :
    node_value_map (KP.insert_map m_node k retval_2)
      (KP.insert_map m1 k &(retval_2 # "blist" ->ₛ "val"))).
  { eapply node_value_map_insert__add_final; eauto. }
  assert (Hcontain_new :
    contain_all_addrs (KP.insert_map m_node k retval_2)
      (retval_2 :: l)).
  { eapply contain_all_addrs_insert_cons; eauto. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth (retval % 211) retval_2 lh)
      (b' b (retval % 211) retval_2)).
  { eapply repr_all_heads_update; eauto. }
  assert (Hcorrect_new :
    contain_all_correct_addrs (KP.insert_map m_node k retval_2)
      (b' b (retval % 211) retval_2)).
  { eapply contain_all_correct_addrs_insert_update; eauto.
    unfold hash_string_k in PreH8.
    unfold NBUCK.
    rewrite PreH8.
    rewrite <- Z.rem_mod_nonneg by lia.
    reflexivity. }
  destruct
    (proj2 (PreH11 (retval % 211) (Znth (retval % 211) lh 0))
      (conj Hidx_lh eq_refl)) as [l_idx Hbidx].
  assert (Hidx_nb : 0 <= retval % 211 < NBUCK).
  { unfold NBUCK. lia. }
  pose proof
    (store_map_store_sll_update_at_idx lh b (retval % 211)
      retval_2 l_idx Hidx_nb PreH2 PreH3 Hbidx) as Hsll_update.
  sep_apply_l_atomic (dll_zero top_ph 0 l PreH1).
  Intros_p Hl.
  subst l.
  subst top_ph.
  Exists retval_2.
  unfold store_hash_skeleton.
  Exists (KP.insert_map m_node k retval_2) (retval_2 :: nil)
    (replace_Znth (retval % 211) retval_2 lh) retval_2 bucks_ph
    (b' b (retval % 211) retval_2).
  split_pure_spatial.
  - unfold NBUCK.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> retval_2).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks_ph).
    cancel
      (PtrArray.full bucks_ph 211
        (replace_Znth (retval % 211) retval_2 lh)).
    simpl dll.
    Exists 0.
    unfold NULL.
    split_pure_spatial.
    + cancel (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> 0).
      cancel (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0).
      sep_apply_r_atomic Hsll_update.
      normalize; repeat cancel.
      sep_apply_r_atomic
        (store_map_name_insert__add_final m_node k retval_2 Hnode_none).
      cancel (store_map store_name m_node).
      sep_apply_r_atomic (ptr_string_name retval_2 key_pre k).
      cancel (&(retval_2 # "blist" ->ₛ "key") # Ptr |-> key_pre).
      cancel (store_string key_pre k).
      sep_apply_r_atomic
        (store_map_uint_insert__add_final m2
          &(retval_2 # "blist" ->ₛ "val") val_pre).
      normalize; repeat cancel.
      cancel (&(retval_2 # "blist" ->ₛ "val") # UInt |-> val_pre).
      cancel (store_map store_uint m2).
      try rewrite dll_nil_equiv.
      normalize.
      repeat cancel.
      all: try (dump_pre_spatial; auto).
      unfold derivable1.
      intros model Hstore.
      exact Hstore.
    + split_pures.
      all: dump_pre_spatial.
      all: try exact PreH2.
      all: reflexivity.
  - split_pures.
    + dump_pre_spatial. exact Hnode_new.
    + dump_pre_spatial. exact Hcontain_new.
    + dump_pre_spatial. exact Hrepr_new.
    + dump_pre_spatial. exact Hcorrect_new.
    + dump_pre_spatial. exact PreH13.
Qed.

Lemma proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p
    (PtrArray.full_Zlength bucks_ph 211
      (replace_Znth (retval % 211) retval_2 lh)).
  Intros_p Hlen_replaced.
  assert (Hlen_lh : Zlength lh = 211).
  { rewrite Zlength_replace_Znth in Hlen_replaced.
    exact Hlen_replaced. }
  assert (Hidx_lh : 0 <= retval % 211 < Zlength lh) by lia.
  assert (Hnode_none : m_node k = None).
  { eapply node_value_map_none__add_final; eauto. }
  assert (Hnode_new :
    node_value_map (KP.insert_map m_node k retval_2)
      (KP.insert_map m1 k &(retval_2 # "blist" ->ₛ "val"))).
  { eapply node_value_map_insert__add_final; eauto. }
  assert (Hcontain_new :
    contain_all_addrs (KP.insert_map m_node k retval_2)
      (retval_2 :: l)).
  { eapply contain_all_addrs_insert_cons; eauto. }
  assert (Hrepr_new :
    repr_all_heads (replace_Znth (retval % 211) retval_2 lh)
      (b' b (retval % 211) retval_2)).
  { eapply repr_all_heads_update; eauto. }
  assert (Hcorrect_new :
    contain_all_correct_addrs (KP.insert_map m_node k retval_2)
      (b' b (retval % 211) retval_2)).
  { eapply contain_all_correct_addrs_insert_update; eauto.
    unfold hash_string_k in PreH9.
    unfold NBUCK.
    rewrite PreH9.
    rewrite <- Z.rem_mod_nonneg by lia.
    reflexivity. }
  destruct
    (proj2 (PreH12 (retval % 211) (Znth (retval % 211) lh 0))
      (conj Hidx_lh eq_refl)) as [l_idx Hbidx].
  assert (Hidx_nb : 0 <= retval % 211 < NBUCK).
  { unfold NBUCK. lia. }
  pose proof
    (store_map_store_sll_update_at_idx lh b (retval % 211)
      retval_2 l_idx Hidx_nb PreH3 PreH4 Hbidx) as Hsll_update.
  subst l.
  Exists retval_2.
  unfold store_hash_skeleton.
  Exists (KP.insert_map m_node k retval_2)
    (retval_2 :: top_ph :: l_tail)
    (replace_Znth (retval % 211) retval_2 lh) retval_2 bucks_ph
    (b' b (retval % 211) retval_2).
  split_pure_spatial.
  - unfold NBUCK.
    cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> retval_2).
    cancel (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks_ph).
    cancel
      (PtrArray.full bucks_ph 211
        (replace_Znth (retval % 211) retval_2 lh)).
    simpl dll.
    Exists top_ph top_down.
    unfold NULL.
    split_pure_spatial.
    + cancel (&(retval_2 # "blist" ->ₛ "down") # Ptr |-> top_ph).
      cancel (&(retval_2 # "blist" ->ₛ "up") # Ptr |-> 0).
      cancel (&(top_ph # "blist" ->ₛ "down") # Ptr |-> top_down).
      cancel (&(top_ph # "blist" ->ₛ "up") # Ptr |-> retval_2).
      cancel (dll top_down top_ph l_tail).
      sep_apply_r_atomic Hsll_update.
      normalize; repeat cancel.
      sep_apply_r_atomic
        (store_map_name_insert__add_final m_node k retval_2 Hnode_none).
      cancel (store_map store_name m_node).
      sep_apply_r_atomic (ptr_string_name retval_2 key_pre k).
      cancel (&(retval_2 # "blist" ->ₛ "key") # Ptr |-> key_pre).
      cancel (store_string key_pre k).
      sep_apply_r_atomic
        (store_map_uint_insert__add_final m2
          &(retval_2 # "blist" ->ₛ "val") val_pre).
      normalize; repeat cancel.
      cancel (&(retval_2 # "blist" ->ₛ "val") # UInt |-> val_pre).
      cancel (store_map store_uint m2).
      try rewrite dll_nil_equiv.
      normalize.
      repeat cancel.
      all: try (dump_pre_spatial; auto).
      unfold derivable1.
      intros model Hstore.
      exact Hstore.
    + split_pures.
      all: dump_pre_spatial.
      all: try exact PreH2.
      all: try exact PreH3.
      all: reflexivity.
  - split_pures.
    + dump_pre_spatial. exact Hnode_new.
    + dump_pre_spatial. exact Hcontain_new.
    + dump_pre_spatial. exact Hrepr_new.
    + dump_pre_spatial. exact Hcorrect_new.
    + dump_pre_spatial. exact PreH14.
Qed.

Lemma proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  Intros m_node l lh top_ph bucks_ph b.
  Exists top_ph bucks_ph lh b l m_node.
  split_pure_spatial.
  - cancel (&(h # "hashtbl" ->ₛ "top") # Ptr |-> top_ph).
    cancel (&(h # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks_ph).
    cancel (dll top_ph 0 l).
    cancel (PtrArray.full bucks_ph 211 lh).
    cancel (store_map store_sll b).
    cancel (store_map store_name m_node).
  - split_pures.
    all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l as [| head l_tail].
  - simpl dll.
    Intros_p Hnull.
    contradiction.
  - simpl dll.
    Intros top_down.
    subst head.
    Exists top_down l_tail.
    split_pure_spatial.
    + cancel (&(h # "hashtbl" ->ₛ "top") # Ptr |-> top_ph).
      cancel (&(top_ph # "blist" ->ₛ "down") # Ptr |-> top_down).
      cancel (&(top_ph # "blist" ->ₛ "up") # Ptr |-> 0).
      cancel (dll top_down top_ph l_tail).
    + dump_pre_spatial.
      reflexivity.
Qed.

