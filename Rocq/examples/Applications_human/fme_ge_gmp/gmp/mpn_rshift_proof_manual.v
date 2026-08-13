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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_rshift_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_rshift_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_1 :
  mpn_rshift_entail_wit_2_inplace_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (0 + 1) with 1 by lia.
  replace (sublist 0 1 l_up_inplace)
    with (sublist 0 (0 + 1) l_up_inplace) by (f_equal; lia).
  rewrite (mpn_lshift_list_to_Z_single_sublist UINT_MOD l_up_inplace 0).
  2: { rewrite PreH8. lia. }
  rewrite list_to_Z_nil.
  rewrite Z.pow_0_r.
  ring_simplify.
  apply mpn_rshift_limb_decompose.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace 0);
      try exact PreH9; lia.
  + lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_2 :
  mpn_rshift_entail_wit_2_inplace_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Z.shiftl_mul_pow2 by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_3 :
  mpn_rshift_entail_wit_2_inplace_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Z.shiftr_div_pow2 by lia.
  symmetry.
  apply Z.quot_div_nonneg.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace 0);
      try exact PreH9; lia.
  + apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_4 :
  mpn_rshift_entail_wit_2_inplace_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_5 :
  mpn_rshift_entail_wit_2_inplace_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_2_inplace : mpn_rshift_entail_wit_2_inplace.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_2.
  + Goal_apply proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_3.
  + Goal_apply proof_of_mpn_rshift_entail_wit_2_inplace_split_goal_5.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_4_inplace : mpn_rshift_entail_wit_4_inplace.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2.
  replace (i + 1 - 1) with i by lia.
  split_pure_spatial.
  - cancel (UIntArray.seg up_pre 0 i l_done_2).
    cancel (UIntArray.seg up_pre i n_pre (sublist i n_pre l_up_inplace)).
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try exact PreH14;
      try (rewrite Znth_sublist by lia;
           replace (i + 1 - i + i) with (i + 1) by lia;
           reflexivity).
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_1 :
  mpn_rshift_entail_wit_5_inplace_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH2.
  apply (mpn_rshift_step_equation l_up_inplace l_done_2 n_pre i cnt_pre
           retval high_limb low_limb tnc);
    try assumption.
  + rewrite PreH7. lia.
  + split; assumption.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_2 :
  mpn_rshift_entail_wit_5_inplace_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH11.
  rewrite Z.shiftr_div_pow2 by lia.
  symmetry.
  apply Z.quot_div_nonneg.
  + apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace i);
      try exact PreH9; lia.
  + apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_3 :
  mpn_rshift_entail_wit_5_inplace_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH2.
  apply (mpn_rshift_done_bound l_up_inplace l_done_2 n_pre i cnt_pre
           high_limb low_limb tnc);
    try assumption.
    + rewrite PreH7. lia.
    + split; assumption.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_4 :
  mpn_rshift_entail_wit_5_inplace_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH2.
  apply (mpn_rshift_done_length l_up_inplace l_done_2 n_pre i
           (Z.lor low_limb
             (unsigned_last_nbits (Z.shiftl high_limb tnc) 32)));
    try assumption.
  rewrite PreH7. lia.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_5_inplace : mpn_rshift_entail_wit_5_inplace.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_2.
  + Goal_apply proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_3.
  + Goal_apply proof_of_mpn_rshift_entail_wit_5_inplace_split_goal_4.
Qed.

Lemma proof_of_mpn_rshift_entail_wit_6_inplace_split_goal_1 :
  mpn_rshift_entail_wit_6_inplace_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_last: i = n_pre - 1) by lia.
  replace n_pre with (i + 1) by lia.
  rewrite <- PreH2.
  exact PreH14.
Qed.

(* This split goal no longer exists in the generated goal interface.
Lemma proof_of_mpn_rshift_entail_wit_6_inplace_split_goal_2 :
  mpn_rshift_entail_wit_6_inplace_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_rshift_entail_wit_6_inplace :
  mpn_rshift_entail_wit_6_inplace.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_entail_wit_6_inplace_split_goal_1.
Qed.

Lemma proof_of_mpn_rshift_return_wit_1_inplace : mpn_rshift_return_wit_1_inplace.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst rp_pre.
  set (last := replace_Znth (i - i) low_limb (sublist i (i + 1) l_up_inplace)).
  Exists (l_done ++ last).
  replace (i + 1) with n_pre by (rewrite PreH5; ring).
  replace (sublist n_pre n_pre l_up_inplace) with (@nil Z) by (rewrite Zsublist_nil by lia; reflexivity).
  split_pure_spatial.
  - sep_apply (UIntArray.seg_merge_to_full up_pre 0 i n_pre l_done last).
    + replace (up_pre + 0 * sizeof(UINT)) with up_pre by nia.
      replace (n_pre - 0) with n_pre by nia.
      unfold UIntArray.seg.
      simpl.
      Intros.
      cancel.
    + split.
      * exact PreH6.
      * rewrite PreH5. ring_simplify. lia.
  - assert (Hlast_single: last = low_limb :: nil).
    { subst last.
      replace (i - i) with 0 by lia.
      assert (Hcond: 0 <= i /\ i < i + 1 /\ i + 1 <= Zlength l_up_inplace) by (rewrite PreH8; lia).
      rewrite (replace_Znth_sublist_head l_up_inplace i (i + 1) low_limb Hcond).
      rewrite Zsublist_nil by lia.
      reflexivity. }
    assert (Hlast_len: Zlength (l_done ++ last) = n_pre).
    { rewrite Hlast_single.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      rewrite PreH9.
      lia. }
    assert (Hlow_bound: 0 <= low_limb < UINT_MOD).
    { rewrite PreH13.
      apply mpn_rshift_quot_limb_bound.
      - apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace i); try exact PreH10; rewrite PreH8; lia.
      - lia. }
    assert (Hlast_bound: list_within_bound UINT_MOD (l_done ++ last)).
    { rewrite Hlast_single.
      apply list_within_bound_app_single.
      - exact PreH11.
      - exact Hlow_bound. }
    assert (Hret: retval = unsigned_last_nbits (Znth 0 l_up_inplace 0 * 2 ^ (32 - cnt_pre)) 32).
    { rewrite PreH14.
      replace (2 ^ (32 - cnt_pre)) with (2 ^ tnc) by (rewrite PreH2; reflexivity).
      reflexivity. }
    assert (Heq: list_to_Z UINT_MOD l_up_inplace =
                   list_to_Z UINT_MOD (l_done ++ last) * 2 ^ cnt_pre +
                   retval ÷ 2 ^ (32 - cnt_pre)).
    { subst last.
      apply (mpn_rshift_return_equation l_up_inplace l_done n_pre i cnt_pre retval low_limb tnc);
        try assumption.
      split; assumption. }
    split_pures.
    + dump_pre_spatial. exact Hlast_len.
    + dump_pre_spatial. exact Hlast_bound.
    + dump_pre_spatial. exact Hret.
    + dump_pre_spatial. exact Heq.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial :
  mpn_rshift_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_self l_up_inplace n_pre) by (symmetry; exact PreH4).
  sep_apply UIntArray.full_to_seg.
  cancel.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_rshift_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_2_split_goal_1 :
  mpn_rshift_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split (i - 1) n_pre i l_up_inplace) by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_2_split_goal_2 :
  mpn_rshift_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_2 :
  mpn_rshift_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_which_implies_wit_2_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_which_implies_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_3_split_goal_1 :
  mpn_rshift_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite (sublist_split i n_pre (i + 1) l_up_inplace) by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_3_split_goal_2 :
  mpn_rshift_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_mpn_rshift_which_implies_wit_3 :
  mpn_rshift_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_rshift_which_implies_wit_3_split_goal_1.
  + Goal_apply proof_of_mpn_rshift_which_implies_wit_3_split_goal_2.
Qed.
