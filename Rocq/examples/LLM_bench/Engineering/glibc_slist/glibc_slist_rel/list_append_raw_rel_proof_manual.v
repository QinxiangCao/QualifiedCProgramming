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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_append_raw_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_append_raw_rel_proof_auto.
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
Require Import list_append_raw_rel_lib.
Local Open Scope sac.

Lemma proof_of_list_append_raw_entail_wit_1 : list_append_raw_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  split_pure_spatial.
  - cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_not_zero' x_pre l1_low_level_spec PreH1).
    Intros.
    unfold list_append_raw_M in PreH2 at 1.
    prog_nf in PreH2.
    unfold list_append_raw_M_before in PreH2 at 1.
    prog_nf in PreH2.
    destruct l1_low_level_spec; [contradiction|].
    prog_nf in PreH2.
    unfold list_append_raw_M_normal in PreH2 at 1.
    prog_nf in PreH2.
    unfold residual_prog_in_list_append_raw_M_call_1.
    dump_pre_spatial.
    exact PreH2.
Qed. 

Lemma proof_of_list_append_raw_return_wit_1 : list_append_raw_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l3_2 ++ v :: l2_low_level_spec).
  split_pure_spatial.
  - sep_apply_right (sllseg_sll x_pre retval l3_2 (v :: l2_low_level_spec)).
    simpl.
    Exists y_pre.
    split_pure_spatial.
    + cancel (&(retval # "list" ->ₛ "next") # Ptr |-> y_pre).
      cancel (&(retval # "list" ->ₛ "data") # Int |-> v).
      cancel.
    + dump_pre_spatial. exact PreH2.
  - split_pure_and_solve.
    prog_nf in PreH1.
    dump_pre_spatial.
    exact PreH1.
Qed.

Lemma proof_of_list_append_raw_return_wit_2 : list_append_raw_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l1_low_level_spec as [| a l1_low_level_spec].
  - Exists l2_low_level_spec.
    split_pure_spatial.
    + simpl.
      cancel.
      repeat (split_pure_spatial || split_pures).
      * Intros_p Hnull.
        cancel.
    + split_pure_and_solve.
      unfold list_append_raw_M in PreH2.
      prog_nf in PreH2.
      unfold list_append_raw_M_before in PreH2.
      prog_nf in PreH2.
      dump_pre_spatial.
      exact PreH2.
  - Exists l2_low_level_spec.
    split_pure_spatial.
    + simpl. Intros y.
      exfalso; apply H; reflexivity.
    + split_pure_and_solve.
      simpl. Intros y.
      exfalso; apply H; reflexivity.
Qed.

Lemma proof_of_list_append_raw_derive_high_level_spec_by_low_level_spec : list_append_raw_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (list_append_raw_M l1_high_level_spec l2_high_level_spec) tt).
  Exists l1_high_level_spec.
  Exists l2_high_level_spec.
  apply sepcon_cancel_end.
  - split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (list_append_raw_M_Hoare
        l1_high_level_spec l2_high_level_spec) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact I | exact Herr0].
  - apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros l3.
    Intros retval_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z)
                ATrue
                (list_append_raw_M l1_high_level_spec l2_high_level_spec)
                (fun r _ => r = app l1_high_level_spec l2_high_level_spec)
                (list_append_raw_M_Hoare
                  l1_high_level_spec l2_high_level_spec)
                ATrue l3 tt H I) as [sigma' [Hret _]].
    subst l3.
    cancel.
Qed.
