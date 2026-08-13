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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_twice_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_twice_rel_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_iter_twice_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_iter_twice_safety_wit_3 : glibc_slist_clean_iter_twice_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  unfold glibc_slist_clean_iter_twice_M_loop in PreH3 at 1. prog_nf in PreH3.
  unfold glibc_slist_clean_iter_twice_M_loop_aux in PreH3 at 1. unfold_loop in PreH3.
  unfold glibc_slist_clean_iter_twice_M_loop_body in PreH3 at 1. prog_nf in PreH3.
  safe_choice_r PreH3.
  unfold glibc_slist_clean_iter_twice_M_loop_M2 in PreH3 at 1.
  destruct l0 as [| v2 l2']; prog_nf in PreH3;
    apply safeExec_assert_seq in PreH3; destruct PreH3 as [Hrange _];
    split_pures; dump_pre_spatial; lia.
  unfold glibc_slist_clean_iter_twice_guardP. simpl. congruence.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_twice_safety_wit_5 : glibc_slist_clean_iter_twice_safety_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  unfold glibc_slist_clean_iter_twice_M_loop in PreH5 at 1. prog_nf in PreH5.
  unfold glibc_slist_clean_iter_twice_M_loop_aux in PreH5 at 1. unfold_loop in PreH5.
  unfold glibc_slist_clean_iter_twice_M_loop_body in PreH5 at 1. prog_nf in PreH5.
  safe_choice_r PreH5.
  unfold glibc_slist_clean_iter_twice_M_loop_M2 in PreH5 at 1. prog_nf in PreH5.
  apply safeExec_assert_seq in PreH5. destruct PreH5 as [_ PreH5].
  prog_nf in PreH5.
  apply safeExec_assert_seq in PreH5. destruct PreH5 as [Hrange _].
  split_pures; dump_pre_spatial; lia.
  unfold glibc_slist_clean_iter_twice_guardP. simpl. congruence.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_twice_entail_wit_1 : glibc_slist_clean_iter_twice_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (@nil Z). Exists l1_low_level_spec.
  split_pure_spatial.
  - unfold sllseg.
    repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial. reflexivity.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_twice_M in PreH2 at 1. prog_nf in PreH2.
    unfold glibc_slist_clean_iter_twice_M_loop_before in PreH2 at 1. prog_nf in PreH2.
    dump_pre_spatial.
    unfold glibc_slist_clean_iter_twice_M_loop at 1. prog_nf.
    exact PreH2.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_twice_entail_wit_2_1 : glibc_slist_clean_iter_twice_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1_2 ++ x :: x_2 :: nil). Exists l0_2.
  split_pure_spatial.
  - sep_apply (sllseg_len1 x_3 x y_2 PreH4).
    sep_apply (sllseg_len1 y_2 x_2 y PreH2).
    sep_apply (sllseg_sllseg x_pre x_3 y_2 l1_2 (x :: nil)).
    sep_apply (sllseg_sllseg x_pre y_2 y (l1_2 ++ x :: nil) (x_2 :: nil)).
    rewrite <- app_assoc. simpl.
    repeat (split_pure_spatial || split_pures).
    + cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_twice_M_loop in PreH5 at 1. prog_nf in PreH5.
    unfold glibc_slist_clean_iter_twice_M_loop_aux in PreH5 at 1. unfold_loop in PreH5.
    unfold glibc_slist_clean_iter_twice_M_loop_body in PreH5 at 1. prog_nf in PreH5.
    safe_choice_r PreH5.
    unfold glibc_slist_clean_iter_twice_M_loop_M2 in PreH5 at 1. prog_nf in PreH5.
    apply safeExec_assert_seq in PreH5. destruct PreH5 as [_ PreH5]. prog_nf in PreH5.
    apply safeExec_assert_seq in PreH5. destruct PreH5 as [_ PreH5]. prog_nf in PreH5.
    unfold continue in PreH5 at 1. prog_nf in PreH5.
    dump_pre_spatial.
    unfold glibc_slist_clean_iter_twice_M_loop at 1. prog_nf.
    exact PreH5.
    unfold glibc_slist_clean_iter_twice_guardP. simpl. congruence.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_twice_entail_wit_2_2 : glibc_slist_clean_iter_twice_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0 as [| v2 l2'].
  - Exists (l1_2 +:: x). Exists (@nil Z).
    split_pure_spatial.
    + sep_apply (sllseg_len1 x_2 x 0 PreH3).
      sep_apply (sllseg_sllseg x_pre x_2 0 l1_2 (x :: nil)).
      unfold sll.
      Intros_p Hnull.
      cancel.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial. exact Hnull.
    + split_pure_and_solve.
      unfold glibc_slist_clean_iter_twice_M_loop in PreH4 at 1. prog_nf in PreH4.
      unfold glibc_slist_clean_iter_twice_M_loop_aux in PreH4 at 1. unfold_loop in PreH4.
      unfold glibc_slist_clean_iter_twice_M_loop_body in PreH4 at 1. prog_nf in PreH4.
      safe_choice_r PreH4.
      unfold glibc_slist_clean_iter_twice_M_loop_M2 in PreH4 at 1. prog_nf in PreH4.
      apply safeExec_assert_seq in PreH4. destruct PreH4 as [_ PreH4]. prog_nf in PreH4.
      unfold continue in PreH4 at 1. prog_nf in PreH4.
      dump_pre_spatial.
      unfold glibc_slist_clean_iter_twice_M_loop at 1. prog_nf.
      exact PreH4.
      unfold glibc_slist_clean_iter_twice_guardP. simpl. congruence.
  - unfold sll. Intros y_bad. Intros. unfold NULL in H. lia.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_twice_return_wit_1 : glibc_slist_clean_iter_twice_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l2_2 as [| v l2'].
  - Exists l1. Exists s.
    split_pure_spatial.
    + sep_apply (sllseg_0_sll x_pre l1). unfold sll at 2.
      Intros_p Hnull.
      cancel.
    + split_pure_and_solve.
      unfold glibc_slist_clean_iter_twice_M_loop in PreH2 at 1. prog_nf in PreH2.
      unfold glibc_slist_clean_iter_twice_M_loop_aux in PreH2 at 1. unfold_loop in PreH2.
      unfold glibc_slist_clean_iter_twice_M_loop_body in PreH2 at 1. prog_nf in PreH2.
      safe_choice_l PreH2.
      unfold glibc_slist_clean_iter_twice_M_loop_M1 in PreH2 at 1. prog_nf in PreH2.
      unfold break in PreH2 at 1. prog_nf in PreH2. rewrite app_nil_r in PreH2.
      dump_pre_spatial. exact PreH2.
  - unfold sll. Intros y_bad. Intros. unfold NULL in H. lia.
Qed. 

Lemma proof_of_glibc_slist_clean_iter_twice_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_iter_twice_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (glibc_slist_clean_iter_twice_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  apply sepcon_cancel_end.
  - repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (glibc_slist_clean_iter_twice_M_Hoare l1_high_level_spec) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact H | exact Herr0].
  - apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros l2.
    Intros r.
    Intros retval_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z * Z)
                (fun _ : unit => range l1_high_level_spec)
                (glibc_slist_clean_iter_twice_M l1_high_level_spec)
                (fun r _ => r = (l1_high_level_spec, list_sum l1_high_level_spec))
                (glibc_slist_clean_iter_twice_M_Hoare l1_high_level_spec)
                ATrue (maketuple l2 r) tt H0 H) as [sigma' [Hret _]].
    unfold maketuple in Hret.
    inversion Hret; subst.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; reflexivity.
Qed.
