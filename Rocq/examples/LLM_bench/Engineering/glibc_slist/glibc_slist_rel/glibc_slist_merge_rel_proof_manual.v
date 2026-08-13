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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_merge_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_merge_rel_proof_auto.
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
Require Import glibc_slist_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_merge_entail_wit_1 : glibc_slist_clean_merge_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (@nil Z : list Z).
  Exists l1_low_level_spec.
  Exists l2_low_level_spec.
  split_pure_spatial.
  - simpl.
    repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial. reflexivity.
  - split_pure_and_solve.
    prop_apply (sll_not_zero' x_pre l1_low_level_spec PreH1).
    Intros.
    destruct l1_low_level_spec as [| a l1_tail]; [contradiction|].
    unfold glibc_slist_clean_merge_M in PreH2. simpl in PreH2.
    unfold glibc_slist_clean_merge_M_loop.
    rewrite bind_ret_l in PreH2.
    dump_pre_spatial.
    exact PreH2.
Qed.
Lemma proof_of_glibc_slist_clean_merge_entail_wit_2 : glibc_slist_clean_merge_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1_2 ++ x_2 :: x :: nil).
  Exists l0_2.
  Exists l0.
  split_pure_spatial.
  - sep_apply (sllseg_len1 cursor x_2 y_3 PreH6).
    sep_apply (sllseg_len1 y_3 x y_2 PreH4).
    sep_apply (sllseg_sllseg cursor y_3 y_2 (x_2 :: nil) (x :: nil)).
    sep_apply (sllseg_sllseg head cursor y_2 l1_2 (x_2 :: x :: nil)).
    sep_apply (store_ptr_undef_store_ptr (&( "node")) y_3).
    cancel.
  - split_pure_and_solve.
    prop_apply (sll_not_zero' y_2 l0_2 PreH1).
    Intros.
    destruct l0_2 as [| l0_head l0_tail]; [contradiction|].
    unfold glibc_slist_clean_merge_M_loop in PreH5.
    unfold glibc_slist_clean_merge_M_loop.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_M_loop_aux in PreH5.
    prog_nf in PreH5.
    unfold_loop in PreH5.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_M_loop_body in PreH5.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_guardP in PreH5.
    prog_nf in PreH5.
    safe_choice_r PreH5.
    unfold glibc_slist_clean_merge_M_loop_M2 in PreH5.
    unfold continue in PreH5.
    simpl in PreH5.
    prog_nf in PreH5.
    dump_pre_spatial.
    exact PreH5.
    discriminate.
Qed.
Lemma proof_of_glibc_slist_clean_merge_return_wit_1 : glibc_slist_clean_merge_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1 ++ l2).
  split_pure_spatial.
  - sep_apply (sll_zero 0 l3_2 ltac:(auto)).
    Intros.
    subst l3_2.
    sep_apply (sllseg_sll head cursor l1 l2).
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l3_2 ltac:(auto)).
    Intros.
    subst l3_2.
    unfold glibc_slist_clean_merge_M_loop in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_merge_M_loop_aux in PreH2.
    prog_nf in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_merge_M_loop_body in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_merge_guardP in PreH2.
    prog_nf in PreH2.
    safe_choice_l PreH2.
    unfold glibc_slist_clean_merge_M_loop_M1 in PreH2.
    unfold break in PreH2.
    unfold glibc_slist_clean_merge_M_after_loop in PreH2.
    unfold glibc_slist_clean_merge_M_loop_end in PreH2.
    prog_nf in PreH2. 
    dump_pre_spatial.
    exact PreH2.
Qed.
Lemma proof_of_glibc_slist_clean_merge_return_wit_2 : glibc_slist_clean_merge_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1 ++ (x_2 :: x :: nil) ++ l0).
  split_pure_spatial.
  - sep_apply (sll_zero 0 l0_2 ltac:(auto)).
    Intros.
    sep_apply (sllseg_len1 y x y_2 PreH4).
    sep_apply (sllseg_len1 cursor x_2 y PreH6).
    sep_apply (sllseg_sllseg cursor y y_2 (x_2 :: nil) (x :: nil)).
    sep_apply (sllseg_sllseg head cursor y_2 l1 (x_2 :: x :: nil)).
    sep_apply (sllseg_sll head y_2 (l1 ++ x_2 :: x :: nil) l0).
    replace ((l1 ++ x_2 :: x :: nil) ++ l0) with
      (l1 ++ (x_2 :: x :: nil) ++ l0).
    2: { rewrite app_assoc. reflexivity. }
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l0_2 ltac:(auto)).
    Intros.
    subst l0_2.
    unfold glibc_slist_clean_merge_M_loop in PreH5.
    unfold glibc_slist_clean_merge_M_loop.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_M_loop_aux in PreH5.
    prog_nf in PreH5.
    unfold_loop in PreH5.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_M_loop_body in PreH5.
    prog_nf in PreH5.
    unfold glibc_slist_clean_merge_guardP in PreH5.
    prog_nf in PreH5.
    safe_choice_r PreH5.
    unfold glibc_slist_clean_merge_M_loop_M2 in PreH5.
    unfold break in PreH5.
    unfold glibc_slist_clean_merge_M_after_loop in PreH5.
    unfold glibc_slist_clean_merge_M_loop_end in PreH5.
    prog_nf in PreH5.
    dump_pre_spatial.
    exact PreH5.
    discriminate.
Qed.
Lemma proof_of_glibc_slist_clean_merge_return_wit_3 : glibc_slist_clean_merge_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l2_low_level_spec.
  split_pure_spatial.
  - sep_apply (sll_zero 0 l1_low_level_spec ltac:(auto)).
    Intros_p Hnil.
    subst l1_low_level_spec.
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l1_low_level_spec ltac:(auto)).
    Intros.
    subst l1_low_level_spec.
    unfold glibc_slist_clean_merge_M in PreH2.
    simpl in PreH2.
    rewrite bind_ret_l in PreH2.
    dump_pre_spatial.
    exact PreH2.
Qed.

Lemma proof_of_glibc_slist_clean_merge_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_merge_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (glibc_slist_clean_merge_M
      l1_high_level_spec l2_high_level_spec) tt).
  Exists l1_high_level_spec.
  Exists l2_high_level_spec.
  apply sepcon_cancel_end.
  - split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (glibc_slist_clean_merge_M_Hoare
        l1_high_level_spec l2_high_level_spec) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact I | exact Herr0].
  - apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros l3_2.
    Intros retval_2.
    Exists l3_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z)
                ATrue
                (glibc_slist_clean_merge_M
                  l1_high_level_spec l2_high_level_spec)
                (fun r _ =>
                  Permutation r
                    (app l1_high_level_spec l2_high_level_spec))
                (glibc_slist_clean_merge_M_Hoare
                  l1_high_level_spec l2_high_level_spec)
                ATrue l3_2 tt H I) as [sigma' [Hperm _]].
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. exact Hperm.
Qed.
