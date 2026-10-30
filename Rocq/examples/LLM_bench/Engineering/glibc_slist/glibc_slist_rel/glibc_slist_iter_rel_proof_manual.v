From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_rel_proof_auto.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_iter_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_iter_safety_wit_3 : glibc_slist_clean_iter_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  unfold glibc_slist_clean_iter_M_loop in PreH3 at 1.
  unfold glibc_slist_clean_iter_M_loop_end in PreH3 at 1.
  prog_nf in PreH3.
  unfold glibc_slist_clean_iter_M_loop_aux in PreH3 at 1.
  unfold_loop in PreH3.
  prog_nf in PreH3.
  unfold glibc_slist_clean_iter_M_loop_body in PreH3 at 1.
  prog_nf in PreH3.
  unfold glibc_slist_clean_iter_guardP in PreH3.
  prog_nf in PreH3.
  safe_choice_r PreH3.
  - unfold glibc_slist_clean_iter_M_loop_M2 in PreH3 at 1.
    prog_nf in PreH3.
    apply safeExec_assert_seq in PreH3 as [Hbounds _].
    split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
  - discriminate.
Qed.
Lemma proof_of_glibc_slist_clean_iter_entail_wit_1 : glibc_slist_clean_iter_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists nil.
  Exists l1_low_level_spec.
  split_pure_spatial.
  - simpl.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_M in PreH2 at 1.
    unfold glibc_slist_clean_iter_M_loop_before in PreH2 at 1.
    prog_nf in PreH2.
    dump_pre_spatial.
    unfold glibc_slist_clean_iter_M_loop.
    unfold glibc_slist_clean_iter_M_loop_end.
    prog_nf.
    exact PreH2.
Qed.
Lemma proof_of_glibc_slist_clean_iter_entail_wit_2 : glibc_slist_clean_iter_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1_2 ++ x :: nil).
  Exists l0.
  split_pure_spatial.
  - sep_apply_right (sllseg_sllseg x_pre x_2 y l1_2 (x :: nil)).
    cancel.
    sep_apply_right (sllseg_len1 x_2 x y PreH2).
    cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_M_loop in PreH3 at 1.
    unfold glibc_slist_clean_iter_M_loop_end in PreH3 at 1.
    prog_nf in PreH3.
    unfold glibc_slist_clean_iter_M_loop_aux in PreH3 at 1.
    unfold_loop in PreH3.
    prog_nf in PreH3.
    unfold glibc_slist_clean_iter_M_loop_body in PreH3 at 1.
    prog_nf in PreH3.
    unfold glibc_slist_clean_iter_guardP in PreH3.
    prog_nf in PreH3.
    safe_choice_r PreH3.
    + unfold glibc_slist_clean_iter_M_loop_M2 in PreH3 at 1.
      prog_nf in PreH3.
      apply safeExec_assert_seq in PreH3 as [_ PreH3].
      unfold continue in PreH3 at 1.
      prog_nf in PreH3.
      dump_pre_spatial.
      unfold glibc_slist_clean_iter_M_loop.
      unfold glibc_slist_clean_iter_M_loop_end.
      prog_nf.
      exact PreH3.
    + discriminate.
Qed.
Lemma proof_of_glibc_slist_clean_iter_return_wit_1 : glibc_slist_clean_iter_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1 ++ l2_2).
  Exists s.
  split_pure_spatial.
  - sep_apply_right (sllseg_sll x_pre 0 l1 l2_2).
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l2_2 eq_refl).
    Intros.
    subst l2_2.
    unfold glibc_slist_clean_iter_M_loop in PreH2 at 1.
    unfold glibc_slist_clean_iter_M_loop_end in PreH2 at 1.
    prog_nf in PreH2.
    unfold glibc_slist_clean_iter_M_loop_aux in PreH2 at 1.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_iter_M_loop_body in PreH2 at 1.
    prog_nf in PreH2.
    unfold glibc_slist_clean_iter_guardP in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2.
    unfold glibc_slist_clean_iter_M_loop_M1 in PreH2 at 1.
    prog_nf in PreH2.
    unfold break in PreH2 at 1.
    prog_nf in PreH2.
    dump_pre_spatial.
    unfold maketuple.
    exact PreH2.
Qed.

Lemma proof_of_glibc_slist_clean_iter_low_level_spec_entail_high_level_spec : glibc_slist_clean_iter_low_level_spec_entail_high_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (glibc_slist_clean_iter_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  apply sepcon_cancel_end.
  - repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (glibc_slist_clean_iter_M_Hoare l1_high_level_spec) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact H | exact Herr0].
  - Intros_r retval.
    apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros l2.
    Intros r.
    Intros.
    destruct (@Hoare_safeexec_compose unit (list Z * Z)
                (fun _ : unit => range l1_high_level_spec)
                (glibc_slist_clean_iter_M l1_high_level_spec)
                (fun r _ => r = (l1_high_level_spec, list_sum l1_high_level_spec))
                (glibc_slist_clean_iter_M_Hoare l1_high_level_spec)
                ATrue (maketuple l2 r) tt H0 H) as [sigma' [Hret _]].
    unfold maketuple in Hret.
    inversion Hret; subst.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; reflexivity.
Qed.
