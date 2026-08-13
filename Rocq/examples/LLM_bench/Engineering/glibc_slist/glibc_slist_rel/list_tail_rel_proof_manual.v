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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_tail_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_tail_rel_proof_auto.
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
Require Import list_tail_rel_lib.
Local Open Scope sac.

Lemma proof_of_list_tail_entail_wit_1 : list_tail_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists nil.
  Exists l1_low_level_spec.
  split_pure_spatial.
  - simpl (sllseg x_pre x_pre nil).
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - split_pure_and_solve.
    prop_apply (sll_not_zero' x_pre l1_low_level_spec PreH1).
    Intros.
    unfold list_tail_M in PreH2 at 1.
    prog_nf in PreH2.
    unfold list_tail_M_loop_before in PreH2 at 1.
    prog_nf in PreH2.
    safe_step PreH2.
    unfold list_tail_M_loop, list_tail_M_loop_end.
    unfold list_tail_M_loop_end in PreH2.
    dump_pre_spatial.
    prog_nf in PreH2.
    prog_nf.
    exact PreH2.
Qed. 
Lemma proof_of_list_tail_entail_wit_2 : list_tail_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1_2 ++ x_2 :: nil).
  Exists l0.
  split_pure_spatial.
  - sep_apply_right (sllseg_sllseg x_pre x y l1_2 (x_2 :: nil)).
    cancel.
    sep_apply_right (sllseg_len1 x x_2 y PreH4).
    cancel.
  - split_pure_and_solve.
    prop_apply (sll_not_zero' y l0 PreH1).
    Intros.
    unfold list_tail_M_loop in PreH3 at 1.
    prog_nf in PreH3.
    unfold list_tail_M_loop_aux in PreH3 at 1.
    prog_nf in PreH3.
    unfold_loop in PreH3.
    prog_nf in PreH3.
    unfold list_tail_M_loop_body in PreH3 at 1.
    prog_nf in PreH3.
    unfold list_tail_guardP in PreH3 at 1.
    prog_nf in PreH3.
    safe_choice_r PreH3.
    + unfold list_tail_M_loop_M2 in PreH3 at 1.
      prog_nf in PreH3.
      unfold continue in PreH3 at 1.
      prog_nf in PreH3.
      unfold list_tail_M_loop, list_tail_M_loop_end.
      dump_pre_spatial.
      prog_nf.
      exact PreH3.
Qed. 
Lemma proof_of_list_tail_return_wit_1 : list_tail_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l1.
  Exists x_2.
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l0 eq_refl).
    Intros.
    cancel.
  - split_pure_and_solve.
    sep_apply_left (sll_zero 0 l0 eq_refl).
    Intros.
    unfold list_tail_M_loop in PreH3 at 1.
    prog_nf in PreH3.
    unfold list_tail_M_loop_aux in PreH3 at 1.
    prog_nf in PreH3.
    unfold_loop in PreH3.
    prog_nf in PreH3.
    unfold list_tail_M_loop_body in PreH3 at 1.
    prog_nf in PreH3.
    unfold list_tail_guardP in PreH3 at 1.
    prog_nf in PreH3.
    safe_choice_l PreH3.
    + unfold list_tail_M_loop_M1 in PreH3 at 1.
      prog_nf in PreH3.
      unfold break in PreH3 at 1.
      prog_nf in PreH3.
      unfold list_tail_M_loop_end.
      dump_pre_spatial.
      prog_nf.
      exact PreH3.
Qed. 

Lemma proof_of_list_tail_derive_high_level_spec_by_low_level_spec : list_tail_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (sll_not_zero' x_pre l1_high_level_spec H).
  Intros.
  rename H0 into Hnonempty.
  Exists (MonadErr.nrm (list_tail_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  apply sepcon_cancel_end.
  - repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial.
      apply safeExec_monad_Atrue_finnal.
      destruct (list_tail_M_Hoare l1_high_level_spec Hnonempty) as [_ Herr].
      intro Herr0.
      eapply Herr; [exact I | exact Herr0].
    + dump_pre_spatial. exact H.
  - apply derivable1_wand_sepcon_adjoint.
    cancel.
    Intros l2_2.
    Intros v_2.
    Intros retval_2.
    Exists l2_2.
    Exists v_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z * Z)
                ATrue
                (list_tail_M l1_high_level_spec)
                (fun r _ => let '(prefix, last) := r in
                            l1_high_level_spec = prefix ++ (last :: nil))
                (list_tail_M_Hoare l1_high_level_spec Hnonempty)
                ATrue (maketuple l2_2 v_2) tt H0 I) as [sigma' [Hret _]].
    simpl in Hret.
    split_pure_spatial.
    + cancel.
      reflexivity.
    + split_pures; dump_pre_spatial; auto.
Qed.
