From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_set_ui_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_set_ui_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_set_ui_entail_wit_1 : mpz_set_ui_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap_2).
  Intros_p Hcap_range.
  Exists ptr_2 cap_2 size_2.
  sep_apply
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr_2 (Zabs old) (Zabs size_2) cap_2 cap_2);
    try lia; try apply Z.abs_nonneg; try exact PreH2.
  rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - LLM_pre_process ltac:(int_auto).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    change Int.max_signed with 2147483647 in Hcap_range.
    int_auto.
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_1 : mpz_set_ui_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_2 : mpz_set_ui_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_spatial : mpz_set_ui_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic
    (UIntArray.undef_full_split_to_undef_seg retval 1 (Z.max 1 cap)).
  - LLM_pre_process ltac:(int_auto).
  - cancel.
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2 : mpz_set_ui_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_set_ui_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mpz_set_ui_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_mpz_set_ui_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_1 : mpz_set_ui_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_2 : mpz_set_ui_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold same_sign.
  left.
  split; lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_spatial : mpz_set_ui_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (x_pre :: nil).
  replace (Zabs 1) with 1 by lia.
  replace (Zabs x0) with x_pre by lia.
  sep_apply_l_atomic (UIntArray.seg_single rp_addr_v 0 x_pre).
  rewrite UIntArray.seg_to_full.
  replace (0 + 1 - 0) with 1 by lia.
  replace (0 + 1) with 1 by lia.
  replace (rp_addr_v + 0) with rp_addr_v by lia.
  split_pure_spatial.
  - LLM_pre_process ltac:(int_auto).
    rewrite Zlength_cons, Zlength_nil.
    replace (rp_addr_v + 0 * sizeof(UINT)) with rp_addr_v by lia.
    cancel.
    change (Z.succ 0) with 1.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite list_to_Z_single.
      repeat split; simpl; unfold UINT_MOD in *; lia.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_cons, Zlength_nil.
      lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1 : mpz_set_ui_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_set_ui_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mpz_set_ui_return_wit_1_split_goal_1.
  - Goal_apply proof_of_mpz_set_ui_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_1 : mpz_set_ui_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_2 : mpz_set_ui_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold same_sign.
  left.
  split; lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_spatial : mpz_set_ui_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hx0 : x0 = 0) by lia.
  subst x0.
  rewrite Z.abs_0.
  sep_apply
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr (Zabs old) (Zabs size) 0 cap);
    try lia; try apply Z.abs_nonneg; try exact PreH2.
  rewrite UIntArray.undef_full_empty.
    unfold mpd_store_Z_compact, mpd_store_list.
    Exists (@nil Z).
    rewrite UIntArray.full_empty.
    split_pure_spatial.
    + LLM_pre_process ltac:(int_auto).
    + split_pures.
      * dump_pre_spatial.
        rewrite list_to_Z_nil.
        repeat split; simpl; try lia; try exact I.
      * dump_pre_spatial.
        simpl.
        rewrite Zlength_nil.
        lia.
      * dump_pre_spatial.
        simpl.
        rewrite Zlength_nil.
        reflexivity.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2 : mpz_set_ui_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_set_ui_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mpz_set_ui_return_wit_2_split_goal_1.
  - Goal_apply proof_of_mpz_set_ui_return_wit_2_split_goal_2.
Qed.

