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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_back_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_iter_back_rel_proof_auto.
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
Require Import glibc_slist_iter_back_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_iter_back_safety_wit_3 : glibc_slist_clean_iter_back_safety_wit_3.
Proof.
  pre_process.
  subst_eqs.
  unfold residual_prog_in_glibc_slist_clean_iter_back_M_call_1 in PreH1 at 1.
  unfold maketuple in PreH1 at 1.
  prog_nf in PreH1.
  unfold safeExec, safe, weakestpre in PreH1.
  simpl in PreH1.
  destruct PreH1 as [? [_ [Hsafe _]]].
  assert (Hrng : -2147483648 <= r + v <= 2147483647).
  { destruct (Z_le_dec (-2147483648) (r + v));
      destruct (Z_le_dec (r + v) 2147483647); try lia.
    all: exfalso; apply Hsafe; left; intro; lia. }
  split_pures; dump_pre_spatial; lia.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_entail_wit_1 : glibc_slist_clean_iter_back_entail_wit_1.
Proof.
  pre_process.
  subst_eqs.
  sep_apply_left (sll_not_zero x_pre l1_low_level_spec PreH1).
  Intros x_next.
  Intros v.
  Intros ltail.
  subst_eqs.
  Exists x_next.
  Exists v.
  Exists ltail.
  split_pure_spatial.
  - entailer!.
  - split_pure_and_solve.
    + dump_pre_spatial.
      unfold range in *.
      destruct PreH2 as [Hz Hf].
      split.
      * rewrite Zlength_cons in Hz. lia.
      * inversion Hf; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_back_entail_wit_2 : glibc_slist_clean_iter_back_entail_wit_2.
Proof.
  pre_process.
  subst_eqs.
  Exists l2.
  Exists v_2.
  split_pure_spatial.
  - entailer!.
  - split_pure_and_solve.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_back_return_wit_1 : glibc_slist_clean_iter_back_return_wit_1.
Proof.
  pre_process.
  subst_eqs.
  Exists (v :: ltail_2).
  Exists (r_2 + v).
  split_pure_spatial.
  - sep_apply (sllseg_len1 x_pre v x_next PreH5).
    sep_apply (sllseg_sll x_pre x_next (v :: nil) ltail_2).
    simpl.
    entailer!.
  - split_pure_and_solve.
    prog_nf in PreH1.
    unfold residual_prog_in_glibc_slist_clean_iter_back_M_call_1 in PreH1.
    cbn in PreH1.
    apply safeExec_assert_seq in PreH1 as [_ PreH1].
    dump_pre_spatial.
    exact PreH1.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_back_return_wit_2 : glibc_slist_clean_iter_back_return_wit_2.
Proof.
  pre_process.
  subst_eqs.
  Exists l1_low_level_spec.
  Exists 0.
  transitivity (“ l1_low_level_spec = nil ” && emp).
  - apply (sll_zero 0 l1_low_level_spec); auto.
  - Intros.
    subst.
    split_pure_spatial.
    + simpl.
      entailer!.
    + split_pure_and_solve.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_iter_back_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists (MonadErr.nrm
    (glibc_slist_clean_iter_back_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros l2.
    Intros r.
    Intros retval_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z * Z)
                (fun _ : unit => range l1_high_level_spec)
                (glibc_slist_clean_iter_back_M l1_high_level_spec)
                (fun r _ => r = (l1_high_level_spec, list_sum l1_high_level_spec))
                (glibc_slist_clean_iter_back_M_Hoare l1_high_level_spec)
                ATrue (maketuple l2 r) tt H0 H) as [sigma' [Hret _]].
    unfold maketuple in Hret.
    inversion Hret; subst.
    entailer!.
  - apply safeExec_monad_Atrue_finnal.
    destruct (glibc_slist_clean_iter_back_M_Hoare l1_high_level_spec) as [_ Herr].
    intro Herr0.
    eapply Herr; [exact H | exact Herr0].
Qed.

Lemma proof_of_glibc_slist_clean_iter_back_derive_low_level_spec_aux_by_low_level_spec : glibc_slist_clean_iter_back_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  subst_eqs.
  destruct (safeExec_bind (glibc_slist_clean_iter_back_M l1_low_level_spec_aux) cont_low_level_spec_aux ATrue X_low_level_spec_aux H0) as [X_low_level_spec [Hcall Hcont]].
  Exists X_low_level_spec.
  Exists l1_low_level_spec_aux.
  split_pure_spatial.
  - entailer!.
    apply derivable1_wand_sepcon_adjoint.
    Intros l2_2.
    Intros r_2.
    Intros retval_2.
    Intros.
    Exists l2_2.
    Exists r_2.
    Exists retval_2.
    split_pure_spatial.
    + entailer!.
    + entailer!.
      specialize (Hcont ATrue (maketuple l2_2 r_2) H1).
      eapply safeExec_proequiv.
      * symmetry. apply bind_ret_l.
      * exact Hcont.
  - split_pure_and_solve.
Qed.
