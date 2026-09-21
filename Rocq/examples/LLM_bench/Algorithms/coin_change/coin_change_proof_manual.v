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
From SimpleC.EE.LLM_bench.Algorithms.coin_change Require Import coin_change_goal.
From SimpleC.EE.LLM_bench.Algorithms.coin_change Require Import coin_change_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.
From AUXLib Require Import MonotonicList.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.




Lemma proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (1 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&( "dp" )) 0 1).
    replace (0 + 1) with 1 by lia.
    sep_apply_l_atomic (IntArray.undef_seg_split_to_undef_seg (&( "dp" )) 1 (amount_pre + 1) 100001 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    split; [reflexivity | change (Forall (eq 0) (@nil Z)); constructor].
Qed.

Lemma proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.seg_Zlength (&( "dp" )) 0 (j + 1) (dp_l_2 ++ 0 :: nil)).
  Intros.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply DpPrefixZeroed_snoc_zero; eauto; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.seg_Zlength (&( "dp" )) 0 j dp_l_2). Intros.
  assert (j = amount_pre + 1) by lia. subst j.
  Exists dp_l_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_full (&( "dp" )) 0 (amount_pre + 1) dp_l_2).
    replace ((&( "dp" )) + 0 * sizeof(INT)) with (&( "dp" )) by lia.
    replace (amount_pre + 1 - 0) with (amount_pre + 1) by lia.
    rewrite (IntArray.undef_seg_empty (&( "dp" )) (amount_pre + 1)) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    change (DpReachableTable nil dp_l_2 (amount_pre + 1)).
    eapply DpPrefixZeroed_to_DpReachableTable_nil; eauto; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength coins_pre coinsSize_pre coins_l). Intros.
  assert (Hcoin : 1 <= Znth i coins_l 0).
  { apply (proj1 (Forall_Znth (Z.le 1) 0 _) PreH8); lia. }
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    destruct PreH9 as [Hbool Htable]. split; [exact Hbool |].
    split; intros k Hk.
    + rewrite ReachableAmount_app_single_below by lia. apply Htable; lia.
    + apply Htable; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_5_1 : coinChange_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp" )) (amount_pre + 1) (replace_Znth j 1 dp_l_2)).
  Intros.
  Exists (replace_Znth j 1 dp_l_2).
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply DpCoinInnerProgress_replace_current; eauto; try lia.
    rewrite Zlength_replace_Znth in H. lia.
Qed.

Lemma proof_of_coinChange_entail_wit_5_2 : coinChange_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    destruct PreH13 as [Hbool [Hprefix Hsuffix]].
    split; [exact Hbool |]. split; intros k Hk.
    + destruct (Z.eq_dec k j) as [-> | Hneq].
      * split.
        -- intro Hcell. apply ReachableAmount_app_l.
           apply (proj1 (Hsuffix j ltac:(lia))); exact Hcell.
        -- intro Hreach.
           destruct (ReachableAmount_app_single_inv (sublist 0 i coins_l) coin j ltac:(lia) Hreach)
             as [Hprev | [_ Hminus]].
           ++ apply (proj2 (Hsuffix j ltac:(lia))); exact Hprev.
           ++ apply (proj2 (Hprefix (j - coin) ltac:(lia))) in Hminus.
              contradiction.
      * apply Hprefix; lia.
    + apply Hsuffix; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_6_1 : coinChange_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength coins_pre coinsSize_pre coins_l). Intros.
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite (sublist_0_succ_app 0 coins_l i) by lia.
    rewrite <- PreH7.
    destruct PreH12 as [Hbool [Hprefix Hsuffix]].
    split; [exact Hbool |]. intros k Hk. apply Hprefix; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_6_2 : coinChange_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength coins_pre coinsSize_pre coins_l). Intros.
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite (sublist_0_succ_app 0 coins_l i) by lia.
    destruct PreH9 as [Hbool Htable].
    split; [exact Hbool |]. intros k Hk.
    rewrite ReachableAmount_app_single_below by lia.
    apply Htable; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength coins_pre coinsSize_pre coins_l). Intros.
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + replace i with (Zlength coins_l) in PreH8 by lia.
      rewrite sublist_self in PreH8 by reflexivity. exact PreH8.
    + unfold NoReachableAbove. intros k Hk; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_8 : coinChange_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists dp_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    intros k Hk Hreach.
    destruct (Z.eq_dec k res) as [-> | Hneq].
    + pose proof (proj2 (proj2 PreH5 res ltac:(lia)) Hreach) as Hnz.
      contradiction.
    + apply (PreH6 k); [lia | exact Hreach].
Qed.

Lemma proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - prop_apply (IntArray.undef_seg_valid (&( "dp" )) (amount_pre + 1) 100001). Intros.
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "dp" )) (amount_pre + 1) dp_l).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "dp" )) (amount_pre + 1)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 (amount_pre + 1) 100001 ltac:(lia)).
    simpl. replace ((&( "dp" )) + 0) with (&( "dp" )) by lia.
    cancel.
  - dump_pre_spatial.
    apply MaxReachableAmount_intro_no_above; try assumption; try lia.
    replace res with 0 by lia. apply ReachableAmount_zero.
Qed.

Lemma proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - prop_apply (IntArray.undef_seg_valid (&( "dp" )) (amount_pre + 1) 100001). Intros.
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "dp" )) (amount_pre + 1) dp_l).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "dp" )) (amount_pre + 1)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 (amount_pre + 1) 100001 ltac:(lia)).
    simpl. replace ((&( "dp" )) + 0) with (&( "dp" )) by lia.
    cancel.
  - dump_pre_spatial.
    apply MaxReachableAmount_intro_no_above; try assumption; try lia.
    apply (proj1 (proj2 PreH5 res ltac:(lia))); exact PreH1.
Qed.