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

Lemma proof_of_hashtbl_clear_entail_wit_1 : hashtbl_clear_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (PtrArray.full_Zlength h_bucks 211 lh_2).
  Intros_p Hlength.
  assert (Hbounds0 : 0 <= 0 < Zlength lh_2) by lia.
  destruct
    (proj2 (PreH3 0 (Znth 0 lh_2 0))
      (conj Hbounds0 eq_refl))
    as [li Hbucket].
  assert (Hnonnegative :
    forall a value, b_2 a = Some value -> 0 <= a).
  { intros a [head bucket] Hlookup.
    destruct (proj1 (PreH3 a head)) as [Hbounds _].
    { exists bucket.
      exact Hlookup. }
    lia. }
  assert (Hremaining :
    remaining_after_bucket_index m1_node_2 m1_node_2 0).
  { unfold remaining_after_bucket_index.
    intros k p.
    split.
    - intro Hlookup.
      split; [exact Hlookup |].
      pose proof (Z.mod_pos_bound (hash_string k) NBUCK).
      unfold NBUCK in *.
      lia.
    - intros [Hlookup _].
      exact Hlookup. }
  sep_apply
    (PtrArray.full_split_to_missing_i
      h_bucks 0 211 lh_2 0 ltac:(lia)).
  sep_apply
    (store_map_split store_sll 0
      (Znth 0 lh_2 0, li) b_2 Hbucket).
  simpl store_sll.
  sep_apply
    (store_map_missing_zero_to_missing_first__clear_setup
      (addr * list addr) store_sll b_2 Hnonnegative).
  prop_apply_p
    (sll_nodup__clear_transition (Znth 0 lh_2 0) li).
  Intros_p Hnodup.
  prop_apply_p
    (store_name_map_injective_all__clear_transition m1_node_2).
  Intros_p Hinjective.
  destruct
    (bucket_key_list_exists_remaining__clear_transition
      m1_node_2 m1_node_2 b_2 0 (Znth 0 lh_2 0) li
      Hinjective Hnodup PreH4 Hremaining Hbucket)
    as [ks Hcurrent].
  pose proof (proj1 Hcurrent) as Hkeys.
  Exists (Znth 0 lh_2 0) h_bucks li ks l_2 top_2
    m1_node_2 lh_2 b_2 m1_node_2.
  split_pure_spatial.
  - change (sizeof(PTR)) with ptr_size_Z.
    normalize; repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: first [assumption | lia].
Qed.

Lemma proof_of_hashtbl_clear_entail_wit_2 : hashtbl_clear_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (clear_next_bucket_or_finish__clear_transition
      h_pre_bucks_3 buck_i_2 m1_node_2 m_rem_2 i lh_2 b_2 li_2 ks_i_2
      ltac:(unfold NBUCK; lia) PreH5 PreH6 PreH7 PreH11) as Hclear.
  unfold NBUCK in Hclear.
  assert (Hreframe :
    PtrArray.full h_pre_bucks_3 211
      (replace_Znth i 0 (replace_Znth i buck_i_2 lh_2)) **
    (store_map store_name (KP.remove_keys m_rem_2 ks_i_2) **
     (store_map store_uint m2 **
      (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top_2 **
       (dll top_2 0 l_2 **
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks_3 **
         store_map_missing_first_i_Z store_sll b_2 i))))) |--
    ((PtrArray.full h_pre_bucks_3 211
        (replace_Znth i 0 (replace_Znth i buck_i_2 lh_2)) **
      store_map store_name (KP.remove_keys m_rem_2 ks_i_2)) **
     store_map_missing_first_i_Z store_sll b_2 i) **
    (store_map store_uint m2 **
     (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top_2 **
      (dll top_2 0 l_2 **
       &(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks_3)))).
  { normalize; repeat cancel. }
  rewrite Hreframe.
  rewrite Hclear.
  Split.
  - Intros buck_i li ks_i.
    rename H into Hnext.
    Left.
    Exists buck_i h_pre_bucks_3 li ks_i l_2 top_2
      (KP.remove_keys m_rem_2 ks_i_2) (replace_Znth i 0 lh_2)
      (fun j => if Z.eq_dec j i then Some (0, li_2) else b_2 j)
      m1_node_2.
    split_pure_spatial.
    + cancel (store_map store_name (KP.remove_keys m_rem_2 ks_i_2)).
      cancel (store_map store_uint m2).
      cancel
        ((h_pre_bucks_3 + (i + 1) * sizeof(PTR)) # Ptr |-> buck_i).
      cancel (sll buck_i li).
      cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top_2).
      cancel (dll top_2 0 l_2).
      cancel
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks_3).
      cancel
        (PtrArray.missing_i h_pre_bucks_3 (i + 1) 0 211
          (replace_Znth i 0 lh_2)).
      unfold derivable1.
      auto.
    + destruct Hnext as [Hcontain [Hrepr [Hremaining [Hbounds Hcurrent]]]].
      destruct Hbounds as [Hlo Hhi].
      pose proof Hcurrent as Hcurrent_full.
      destruct Hcurrent as [Hkeys Hcurrent_rest].
      repeat split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: lia.
  - Intros_p Hfinish.
    Right.
    Exists h_pre_bucks_3 l_2 top_2
      (KP.remove_keys m_rem_2 ks_i_2) (replace_Znth i 0 lh_2)
      (fun j => if Z.eq_dec j i then Some (0, li_2) else b_2 j)
      m1_node_2.
    split_pure_spatial.
    + cancel (store_map store_name (KP.remove_keys m_rem_2 ks_i_2)).
      cancel (store_map store_uint m2).
      cancel (&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top_2).
      cancel (dll top_2 0 l_2).
      cancel
        (&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks_3).
      cancel
        (PtrArray.full h_pre_bucks_3 211 (replace_Znth i 0 lh_2)).
    + destruct Hfinish as [Hcontain [Hrepr [Hremaining Hbound]]].
      repeat split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: lia.
Qed.

Lemma proof_of_hashtbl_clear_return_wit_1 : hashtbl_clear_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists top l_2 m_rem_2 m1_node_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      assumption.
    + dump_pre_spatial.
      apply
        (remaining_after_ge_nbuck__clear_final
          m1_node_2 m_rem_2 i).
      * unfold NBUCK.
        lia.
      * assumption.
Qed.

Lemma proof_of_hashtbl_clear_which_implies_wit_1 : hashtbl_clear_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  Intros m1_node l lh top h_bucks b.
  unfold NBUCK, NULL.
  Exists top h_bucks lh b l m1_node.
  split_pure_spatial.
  - normalize; repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption.
Qed.
