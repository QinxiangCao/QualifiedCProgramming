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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_free_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_free_rel_proof_auto.
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
Require Import glibc_slist_free_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_free_entail_wit_1 : glibc_slist_clean_free_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l1_low_level_spec.
  split_pure_spatial.
  - cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_free_M in PreH1 at 1.
    prog_nf in PreH1.
    dump_pre_spatial.
    prog_nf.
    exact PreH1.
Qed. 
Lemma proof_of_glibc_slist_clean_free_entail_wit_2 : glibc_slist_clean_free_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left store_ptr_undef_store_ptr.
    cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_free_M_loop in PreH3 at 1.
    unfold glibc_slist_clean_free_M_loop_aux in PreH3 at 1.
    unfold_loop in PreH3.
    prog_nf in PreH3.
    unfold glibc_slist_clean_free_M_loop_body in PreH3.
    prog_nf in PreH3.
    safe_choice_r PreH3.
    + unfold glibc_slist_clean_free_M_loop_M2 in PreH3.
      prog_nf in PreH3.
      unfold continue in PreH3.
      prog_nf in PreH3.
      dump_pre_spatial.
      unfold glibc_slist_clean_free_M_loop.
      unfold glibc_slist_clean_free_M_loop_aux.
      unfold glibc_slist_clean_free_M_loop_body.
      unfold glibc_slist_clean_free_M_loop_M2.
      unfold continue.
      unfold glibc_slist_clean_free_M_loop_end.
      prog_nf.
      exact PreH3.
    + unfold glibc_slist_clean_free_guardP.
      discriminate.
Qed. 
Lemma proof_of_glibc_slist_clean_free_return_wit_1 : glibc_slist_clean_free_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l1 eq_refl).
  Intros.
  subst_eqs.
  split_pure_spatial.
  - cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_free_M_loop in PreH2 at 1.
    unfold glibc_slist_clean_free_M_loop_aux in PreH2 at 1.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_free_M_loop_body in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2.
    unfold glibc_slist_clean_free_M_loop_M1 in PreH2.
    prog_nf in PreH2.
    unfold break in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_free_M_loop_end in PreH2.
    prog_nf in PreH2.
    dump_pre_spatial.
    exact PreH2.
Qed. 

Lemma proof_of_glibc_slist_clean_free_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_free_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm (glibc_slist_clean_free_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  apply sepcon_cancel_end.
  - split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (glibc_slist_clean_free_M_Hoare l1_high_level_spec) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact I | exact Herr0].
  - apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros_p Hsafe.
    cancel.
Qed.
