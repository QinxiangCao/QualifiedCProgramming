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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_rev_append_twice_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_rev_append_twice_rel_proof_auto.
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
Require Import glibc_slist_rev_append_twice_rel_lib.
Local Open Scope sac.


Lemma proof_of_glibc_slist_clean_rev_append_twice_entail_wit_1 : glibc_slist_clean_rev_append_twice_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l1_low_level_spec. Exists l2_low_level_spec.
  split_pure_spatial.
  - cancel.
  - split_pure_and_solve.
    unfold glibc_slist_clean_rev_append_twice_M in PreH1 at 1.
    prog_nf in PreH1.
    unfold glibc_slist_clean_rev_append_twice_M_loop_before in PreH1 at 1.
    prog_nf in PreH1.
    dump_pre_spatial.
    unfold glibc_slist_clean_rev_append_twice_M_loop at 1.
    prog_nf.
    exact PreH1.
Qed. 


Lemma proof_of_glibc_slist_clean_rev_append_twice_entail_wit_2_1 : glibc_slist_clean_rev_append_twice_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l0_2. Exists (x_3 :: x_2 :: l2_2).
  split_pure_spatial.
  - simpl (sll y (x_3 :: x_2 :: l2_2)).
    Exists x.
    simpl (sll x (x_2 :: l2_2)).
    Exists y_3.
    split_pure_spatial.
    + sep_apply (store_ptr_undef_store_ptr &("t") y_2).
      cancel.
    + split_pures.
      * dump_pre_spatial. exact PreH2.
      * dump_pre_spatial. exact PreH4.
  - split_pure_and_solve.
    unfold glibc_slist_clean_rev_append_twice_M_loop in PreH5 at 1.
    prog_nf in PreH5.
    unfold glibc_slist_clean_rev_append_twice_M_loop_aux in PreH5 at 1.
    prog_nf in PreH5.
    unfold_loop in PreH5.
    prog_nf in PreH5.
    unfold glibc_slist_clean_rev_append_twice_M_loop_body in PreH5 at 1.
    prog_nf in PreH5.
    unfold glibc_slist_clean_rev_append_twice_guardP in PreH5 at 1.
    prog_nf in PreH5.
    safe_choice_r PreH5.
    + unfold glibc_slist_clean_rev_append_twice_M_loop_M2 in PreH5 at 1.
      prog_nf in PreH5.
      unfold continue in PreH5 at 1.
      prog_nf in PreH5.
      dump_pre_spatial.
      unfold glibc_slist_clean_rev_append_twice_M_loop at 1.
      prog_nf.
      exact PreH5.
    + unfold glibc_slist_clean_rev_append_twice_guardP.
      simpl.
      congruence.
Qed. 


Lemma proof_of_glibc_slist_clean_rev_append_twice_entail_wit_2_2 : glibc_slist_clean_rev_append_twice_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (@nil Z). Exists (x_2 :: l2_2).
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l0 eq_refl).
    Intros.
    subst_eqs.
    unfold sll at 1.
    simpl (sll x (x_2 :: l2_2)).
    Exists y_2.
    unfold sll at 2.
    sep_apply_left (store_ptr_undef_store_ptr &("t") 0).
    repeat (split_pure_spatial || split_pures).
    + cancel.
      sepcon_assoc_change.
      reflexivity.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. reflexivity.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l0 eq_refl).
    Intros.
    subst_eqs.
    unfold glibc_slist_clean_rev_append_twice_M_loop in PreH4 at 1.
    prog_nf in PreH4.
    unfold glibc_slist_clean_rev_append_twice_M_loop_aux in PreH4 at 1.
    prog_nf in PreH4.
    unfold_loop in PreH4.
    prog_nf in PreH4.
    unfold glibc_slist_clean_rev_append_twice_M_loop_body in PreH4 at 1.
    prog_nf in PreH4.
    unfold glibc_slist_clean_rev_append_twice_guardP in PreH4 at 1.
    prog_nf in PreH4.
    safe_choice_r PreH4.
    + unfold glibc_slist_clean_rev_append_twice_M_loop_M2 in PreH4 at 1.
      prog_nf in PreH4.
      unfold continue in PreH4 at 1.
      prog_nf in PreH4.
      dump_pre_spatial.
      unfold glibc_slist_clean_rev_append_twice_M_loop at 1.
      prog_nf.
      exact PreH4.
    + unfold glibc_slist_clean_rev_append_twice_guardP.
      simpl.
      congruence.
Qed. 

Lemma proof_of_glibc_slist_clean_rev_append_twice_return_wit_1 : glibc_slist_clean_rev_append_twice_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l2.
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l1 eq_refl).
    Intros.
    subst_eqs.
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l1 eq_refl).
    Intros.
    subst_eqs.
    unfold glibc_slist_clean_rev_append_twice_M_loop in PreH2 at 1.
    prog_nf in PreH2.
    unfold glibc_slist_clean_rev_append_twice_M_loop_aux in PreH2 at 1.
    prog_nf in PreH2.
    unfold_loop in PreH2.
    prog_nf in PreH2.
    unfold glibc_slist_clean_rev_append_twice_M_loop_body in PreH2 at 1.
    prog_nf in PreH2.
    unfold glibc_slist_clean_rev_append_twice_guardP in PreH2 at 1.
    prog_nf in PreH2.
    safe_choice_l PreH2.
    unfold glibc_slist_clean_rev_append_twice_M_loop_M1 in PreH2 at 1.
    prog_nf in PreH2.
    unfold break in PreH2 at 1.
    prog_nf in PreH2.
    dump_pre_spatial.
    exact PreH2.
Qed. 

Lemma proof_of_glibc_slist_clean_rev_append_twice_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_rev_append_twice_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (glibc_slist_clean_rev_append_twice_M
      l1_high_level_spec l2_high_level_spec) tt).
  Exists l1_high_level_spec.
  Exists l2_high_level_spec.
  apply sepcon_cancel_end.
  - split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (glibc_slist_clean_rev_append_twice_M_Hoare
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
                (glibc_slist_clean_rev_append_twice_M
                  l1_high_level_spec l2_high_level_spec)
                (fun r _ => r = app (rev l1_high_level_spec) l2_high_level_spec)
                (glibc_slist_clean_rev_append_twice_M_Hoare
                  l1_high_level_spec l2_high_level_spec)
                ATrue l3 tt H I) as [sigma' [Hret _]].
    subst l3.
    cancel.
Qed.
