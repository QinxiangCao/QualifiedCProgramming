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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_ui_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_ui_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_realloc_return_wit_1_split_goal_spatial :
  mpz_realloc_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH3.
  rewrite PreH9.
  rewrite UIntArray.undef_full_empty.
  repeat cancel.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_2_split_goal_spatial :
  mpz_realloc_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH3.
  cancel.
Qed.

Lemma proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_1_split_goal_spatial :
  mpz_realloc_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite list_to_Z_nil.
      repeat split; simpl; try lia; try exact I.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_nil.
      lia.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_nil.
      reflexivity.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_1 : mpz_realloc_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_2 : mpz_realloc_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (mpd_store_Z_compact_to_mpd_store_Z r__mp_d 0 0).
  sep_apply_l_atomic (mpd_store_Z_to_undef_full r__mp_d 0 0).
  rewrite UIntArray.undef_full_empty.
  sep_apply_l_atomic (UIntArray.undef_seg_to_undef_full r__mp_d 0 size).
  replace (r__mp_d + 0 * sizeof(UINT)) with r__mp_d by lia.
  replace (size - 0) with size by lia.
  repeat cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_1 :
  mrz_realloc_if_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_2 :
  mrz_realloc_if_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial :
  mrz_realloc_if_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Z.max n_pre cap_raw) with cap_raw by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  aggressive_pre_process.
  + exact
      (proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial
        n_pre cap_raw sz_raw ptr_raw PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
  + exact
      (proof_of_mrz_realloc_if_return_wit_1_split_goal_1
        n_pre cap_raw sz_raw ptr_raw PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
  + exact
      (proof_of_mrz_realloc_if_return_wit_1_split_goal_2
        n_pre cap_raw sz_raw ptr_raw PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_1 :
  mrz_realloc_if_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_2 :
  mrz_realloc_if_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial :
  mrz_realloc_if_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Z.max n_pre cap_raw) with (Z.max n_pre 1) by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  aggressive_pre_process.
  + exact
      (proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial
        n_pre cap_raw sz_raw r_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mrz_realloc_if_return_wit_2_split_goal_1
        n_pre cap_raw sz_raw r_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mrz_realloc_if_return_wit_2_split_goal_2
        n_pre cap_raw sz_raw r_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_1 : mpz_set_ui_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ptr_2 cap_2 size_2.
  sep_apply
    (mpd_store_Z_compact_undef_tail_to_undef_split
       ptr_2 (Zabs old) (Zabs size_2) cap_2 cap_2);
    try lia; try apply Z.abs_nonneg; try exact PreH2.
  rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - LLM_pre_process ltac:(int_auto).
  - LLM_pre_process ltac:(int_auto).
    prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap_2).
    Intros Hcap_range.
    split_pures; dump_pre_spatial; try assumption; try lia.
    change Int.max_signed with 2147483647 in H4.
    lia.
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_1 :
  mpz_set_ui_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_2 :
  mpz_set_ui_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_entail_wit_2_split_goal_spatial :
  mpz_set_ui_entail_wit_2_split_goal_spatial.
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
  + exact
      (proof_of_mpz_set_ui_entail_wit_2_split_goal_spatial
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
  + exact
      (proof_of_mpz_set_ui_entail_wit_2_split_goal_1
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
  + exact
      (proof_of_mpz_set_ui_entail_wit_2_split_goal_2
        x_pre x0 old size cap z_callee__mp_alloc retval
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_1 :
  mpz_set_ui_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_2 :
  mpz_set_ui_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold same_sign.
  left.
  split; lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_1_split_goal_spatial :
  mpz_set_ui_return_wit_1_split_goal_spatial.
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
  + exact
      (proof_of_mpz_set_ui_return_wit_1_split_goal_spatial
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mpz_set_ui_return_wit_1_split_goal_1
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  + exact
      (proof_of_mpz_set_ui_return_wit_1_split_goal_2
        x_pre x0 cap cap_new rp_addr_v
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_1 :
  mpz_set_ui_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_2 :
  mpz_set_ui_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold same_sign.
  left.
  split; lia.
Qed.

Lemma proof_of_mpz_set_ui_return_wit_2_split_goal_spatial :
  mpz_set_ui_return_wit_2_split_goal_spatial.
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
  + exact
      (proof_of_mpz_set_ui_return_wit_2_split_goal_spatial
        x_pre x0 old ptr size cap PreH1 PreH2 PreH3 PreH4 PreH5).
  + exact
      (proof_of_mpz_set_ui_return_wit_2_split_goal_1
        x_pre x0 old ptr size cap PreH1 PreH2 PreH3 PreH4 PreH5).
  + exact
      (proof_of_mpz_set_ui_return_wit_2_split_goal_2
        x_pre x0 old ptr size cap PreH1 PreH2 PreH3 PreH4 PreH5).
Qed.
