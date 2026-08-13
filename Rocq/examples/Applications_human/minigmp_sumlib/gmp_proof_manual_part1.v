Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Proof. LLM_pre_process ltac:(int_auto). Qed. 

Lemma proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.  

Lemma proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Proof. LLM_pre_process ltac:(int_auto). Qed. 

Lemma proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (Zlength_nonneg l).
  split_pure_spatial.
  - rewrite UIntArray.full_empty.
    sep_apply UIntArray.undef_full_to_undef_seg.
    split_pure_spatial.
    { cancel. }
    { dump_pre_spatial; reflexivity. }
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2_split_goal_1 :
  mpn_copyi_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split 0 (i + 1) i) ; try lia.
  rewrite <- sublist_single ; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_copyi_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z , mpd_store_list. 
  Exists l l.
  assert (i = n_pre) by lia.
  subst i.
  rewrite sublist_self ; try lia.
  rewrite UIntArray.undef_seg_empty.
  subst n_pre.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try (split; assumption); reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z , mpd_store_list.
  Intros l. 
  Exists l. subst n.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity;
      destruct H; assumption.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1_split_goal_1 :
  mpn_cmp_entail_wit_1_split_goal_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  replace (n_pre - 1 + 1) with (n_pre) by lia.
  rewrite Zsublist_nil ; try lia.
  rewrite Zsublist_nil ; try lia.
  auto.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  replace (n - 1 + 1) with n by lia.
  do 2 (rewrite (sublist_split n n_pre (n + 1)) ; try lia).
  rewrite PreH5.
  rewrite (sublist_single 0 n l1) ; try lia.
  rewrite (sublist_single 0 n l2) ; try lia.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Proof. 
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - unfold mpd_store_Z_compact.
    Exists l1 l2.
    unfold mpd_store_list.
    split_pure_spatial.
    + rewrite <- PreH13, <- PreH14.
      cancel.
    + repeat split_pures; dump_pre_spatial;
        try (repeat split; assumption);
        try assumption; try reflexivity; try lia.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    assert (Znth n l1 0 < Znth n l2 0) by lia.
    unfold UINT_MOD in *.
    rewrite <- PreH7, <- PreH10.
    apply (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l1 l2 n) ; auto ; try lia.
    rewrite <- PreH13, <- PreH14.
    auto.
Qed.

Lemma proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - unfold mpd_store_Z_compact.
    Exists l1 l2.
    unfold mpd_store_list.
    split_pure_spatial.
    + rewrite <- PreH13, <- PreH14.
      cancel.
    + repeat split_pures; dump_pre_spatial;
        try (repeat split; assumption);
        try assumption; try reflexivity; try lia.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    pose proof (list_to_Z_cmp_same_length 4294967296 (ltac:(lia)) l2 l1 n) as Hcmp.
    rewrite <- PreH13, <- PreH14 in Hcmp.
    unfold UINT_MOD in *.
    rewrite <- PreH7, <- PreH10.
    specialize (Hcmp (ltac:(lia)) (ltac:(lia)) (ltac:(auto)) PreH12 PreH9 (ltac:(lia))).
    lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Exists l1 l2.
  unfold mpd_store_list.
  rewrite <- PreH5, <- PreH8.
  rewrite <- PreH11, <- PreH12.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  replace (n + 1) with 0 in * by lia.
  do 2 rewrite sublist_self in * by lia.
  subst.
  all: try reflexivity.
  all: (constructor; [reflexivity | constructor; assumption]).
Qed.

Lemma proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Intros l1 l2.
  Exists l2 l1.
  rewrite <- H0, <- H2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold UINT_MOD in *.
    all: destruct H as (? & ? & Hb1);
      destruct H1 as (? & ? & Hb2).
    + exact Hb1.
    + unfold UINT_MOD; exact Hb2.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l2 l1 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia. 
Qed.

Lemma proof_of_mpn_cmp4_return_wit_4 : mpn_cmp4_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  unfold UINT_MOD in *.
  pose proof list_to_Z_cmp_diff_length 4294967296 (ltac:(lia)) l1 l2 (ltac:(lia)) (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia)).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_3_split_goal_spatial :
  mpn_cmp4_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_3 : mpn_cmp4_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2_split_goal_spatial :
  mpn_cmp4_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1_split_goal_spatial :
  mpn_cmp4_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst.
  cancel.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_cmp4_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_1 :
  mpn_normalized_size_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2_split_goal_2 :
  mpn_normalized_size_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite sublist_self; try lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_2 :
  mpn_normalized_size_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_mpn_normalized_size_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Znth_sublist in PreH1 ; try lia.
  replace (n - 1 + 0) with (n - 1) in * by lia.
  rewrite (sublist_split 0 n (n-1)) in *  ; try lia.
  set (m := n - 1) in *.
  replace n with (m + 1) in * by lia.
  rewrite (sublist_single 0 m l) in * ; try lia.
  rewrite PreH1 in *.
  unfold UINT_MOD in *.
  rewrite list_to_Z_concat in PreH5 ; [ | lia | apply list_within_bound_sublist ; [ lia | lia | tauto] | simpl ; lia].
  sep_apply (UIntArray.full_split_to_seg xp_pre m) ; try lia.
  sep_apply (UIntArray.seg_to_undef_seg xp_pre m ).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg ; try lia.
  sep_apply UIntArray.seg_to_full.
  replace (xp_pre + 0 * sizeof ( UINT )) with (xp_pre) by lia.
  replace (m - 0) with m by lia.
  assert (Hlen_sub: m = Zlength(sublist 0 m l)).
  {
    rewrite Zlength_sublist ; try lia.
  }
  rewrite Hlen_sub at 2.
  rewrite sublist_app_exact1.
  simpl in PreH5.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  assert (n = 0) by lia.
  subst n.
  rewrite Zsublist_nil in * ; try lia.
  unfold mpd_store_list.
  Exists nil.
  split_pure_spatial.
  - change (Zlength (@nil Z)) with 0.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    repeat split; simpl; try assumption; try lia.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_2 : mpn_normalized_size_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Exists (sublist 0 n l).
  rewrite Zlength_sublist ; try lia.
  replace (n - 0) with n by lia.
  pose proof (list_within_bound_sublist UINT_MOD l 0 n (ltac:(lia)) (ltac:(lia)) (ltac:(tauto))).
  split_pure_spatial; [cancel |].
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  rewrite list_last_to_Znth.
  + rewrite Zlength_sublist ; try lia.
    replace (n - 0 -  1) with (n - 1) by lia.
    pose proof (list_within_bound_Znth UINT_MOD UINT_MOD_pos (sublist 0 n l) (n - 1) (ltac:(lia)) (ltac:(tauto))).
    repeat split; try assumption; lia.
  + intro Hnil. rewrite Hnil in PreH1.
    unfold Znth in PreH1. simpl in PreH1.
    contradiction PreH1; destruct (Z.to_nat (n - 1)); reflexivity.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z.
  unfold mpd_store_list.
  Intros l.
  Exists l.
  rewrite <- H0.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    destruct H; assumption.
Qed.
