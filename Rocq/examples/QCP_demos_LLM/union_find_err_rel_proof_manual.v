Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import union_find_err_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.union_find_err_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_uf_find_c_entail_wit_1 : uf_find_c_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial; [cancel | idtac].
  split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; reflexivity).
  dump_pre_spatial.
  rename PreH5 into Hsafe.

  apply (safeExec_proequiv
           (uf_find x_pre)
           ((uf_find_f uf_find) x_pre)
           (equiv (uf_state_of n_pre ps_low_level_spec rs_low_level_spec))
           X_low_level_spec) in Hsafe.
  2: { apply (program_para_equiv uf_find_unfold). }
  unfold uf_find_f in Hsafe at 1.
  prog_nf in Hsafe.
  unfold read_parent in Hsafe at 1.
  prog_nf in Hsafe.
  apply safeExec_assertS_seq in Hsafe.
  apply safeExec_get_bind with (a := Znth x_pre ps_low_level_spec 0) in Hsafe.
  2: {
    intros s [_ Heq].
    cbv [equiv uf_state_equiv] in Heq.
    subst s.
    rewrite uf_state_of_parent_read by lia.
    reflexivity.
  }
  prog_nf in Hsafe.
  apply safeExec_assertS_seq in Hsafe.
  unfold uf_find_after_read at 1.
  refine (safeExec_conseq _ _ _ _ Hsafe _).
  intros s [_ [_ Heq]]; exact Heq.
Qed.

Lemma proof_of_uf_find_c_entail_wit_2 : uf_find_c_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial; [cancel | idtac].
  rename PreH7 into Hsafe.
  assert (Hvalid_p : valid (uf_state_of n_pre ps_low_level_spec rs_low_level_spec) p).
  {
    pose proof Hsafe as Hsafe_valid.
    unfold uf_find_after_read in Hsafe_valid at 1.
    prog_nf in Hsafe_valid.
    safe_choice_r Hsafe_valid.
    apply (safeExec_proequiv
             (y <- uf_find p;; write_parent x_pre y;; return y)
             (y <- (uf_find_f uf_find) p;; write_parent x_pre y;; return y)
             (equiv (uf_state_of n_pre ps_low_level_spec rs_low_level_spec))
             X_low_level_spec) in Hsafe_valid.
    2: {
      apply bind_equiv.
      + apply (program_para_equiv uf_find_unfold).
      + reflexivity.
    }
    unfold uf_find_f in Hsafe_valid at 1.
    prog_nf in Hsafe_valid.
    unfold read_parent in Hsafe_valid at 1.
    prog_nf in Hsafe_valid.
    apply safeExec_assertS_seq in Hsafe_valid.
    unfold safeExec in Hsafe_valid.
    destruct Hsafe_valid as [s [[Hvalid_p_s Heq] _]].
    apply (proj2 (uf_state_equiv_valid
                    (uf_state_of n_pre ps_low_level_spec rs_low_level_spec)
                    s p Heq)).
    exact Hvalid_p_s.
  }
  unfold valid in Hvalid_p; simpl in Hvalid_p.
  split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; reflexivity).
  dump_pre_spatial.
  unfold uf_find_after_read in Hsafe at 1.
  prog_nf in Hsafe.
  safe_choice_r Hsafe.
  unfold uf_find_after_rec.
  exact Hsafe.
Qed.

Lemma proof_of_uf_find_c_entail_wit_4 : uf_find_c_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength parent_pre n_pre (replace_Znth x_pre r ps1_2)).
  Intros_p Hlen.
  rewrite replace_Znth_Zlength in Hlen.
  Exists ps1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH8 into Hsafe.
    unfold applyf in Hsafe.
    unfold uf_find_after_rec in Hsafe at 1.
    prog_nf in Hsafe.
    unfold write_parent in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_update'_bind in Hsafe.
    refine (safeExec_conseq _ _ _ _ Hsafe _).
    intros s [s0 [-> [_ Heq]]].
    cbv [equiv uf_state_equiv] in Heq |- *.
    subst s0.
    rewrite uf_state_of_set_parent_replace by lia.
    reflexivity.
Qed.

Lemma proof_of_uf_find_c_return_wit_2 : uf_find_c_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps_low_level_spec.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia).
    dump_pre_spatial.
    rename PreH7 into Hsafe.
    unfold uf_find_after_read in Hsafe at 1.
    prog_nf in Hsafe.
    safe_choice_l Hsafe.
    exact Hsafe.
Qed.

Lemma proof_of_uf_union_c_entail_wit_1 : uf_union_c_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_uf_union_c_entail_wit_4 : uf_union_c_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps2_2 rs2_2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; symmetry; assumption).
    dump_pre_spatial.
    rename PreH8 into Hsafe.
    unfold applyf in Hsafe.
    prog_nf in Hsafe.
    unfold uf_union_after_find_y in Hsafe at 1.
    prog_nf in Hsafe.
    safe_choice_l Hsafe.
    exact Hsafe.
Qed.

Lemma proof_of_uf_union_c_entail_wit_5 : uf_union_c_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps2_2 rs2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; reflexivity); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH8 into Hsafe.
    unfold applyf in Hsafe.
    prog_nf in Hsafe.
    unfold uf_union_after_find_y in Hsafe at 1.
    prog_nf in Hsafe.
    safe_choice_r Hsafe.
    unfold read_rank in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_get_bind with (a := Znth rx rs2 0) in Hsafe.
    + unfold uf_union_after_rank_rx.
      refine (safeExec_conseq
                (equiv (uf_state_of n_pre ps2_2 rs2))
                (fun s : uf_state => valid s rx /\ equiv (uf_state_of n_pre ps2_2 rs2) s)
                _ X_low_level_spec Hsafe _).
      intros s [_ Heq]; exact Heq.
    + intros s [_ Heq].
      cbv [equiv uf_state_equiv] in Heq.
      subst s.
      rewrite uf_state_of_rank_read by lia.
      reflexivity.
Qed.

Lemma proof_of_uf_union_c_entail_wit_6 : uf_union_c_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps2_2 rs2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; reflexivity); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH9 into Hsafe.
    unfold uf_union_after_rank_rx in Hsafe at 1.
    prog_nf in Hsafe.
    unfold read_rank in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_get_bind with (a := Znth ry rs2 0) in Hsafe.
    + unfold uf_union_after_rank_ry.
      refine (safeExec_conseq
                (equiv (uf_state_of n_pre ps2_2 rs2))
                (fun s : uf_state => valid s ry /\ equiv (uf_state_of n_pre ps2_2 rs2) s)
                _ X_low_level_spec Hsafe _).
      intros s [_ Heq]; exact Heq.
    + intros s [_ Heq].
      cbv [equiv uf_state_equiv] in Heq.
      subst s.
      rewrite uf_state_of_rank_read by lia.
      reflexivity.
Qed.

Lemma proof_of_uf_union_c_entail_wit_7 : uf_union_c_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength parent_pre n_pre (replace_Znth ry rx ps2_2)).
  Intros_p Hlen_replace.
  rewrite replace_Znth_Zlength in Hlen_replace.
  Exists ps2_2 rs2_2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH11 into Hsafe.
    unfold uf_union_after_rank_ry in Hsafe at 1.
    prog_nf in Hsafe.
    safe_choice_l Hsafe.
    unfold write_parent in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_update' in Hsafe.
    refine (safeExec_conseq
              (equiv (uf_state_of n_pre (replace_Znth ry rx ps2_2) rs2_2))
              _ _ X_low_level_spec Hsafe _).
    intros s [s0 [Hs [_ Heq]]].
    subst s.
    cbv [equiv uf_state_equiv] in Heq |- *.
    subst s0.
    rewrite uf_state_of_set_parent_replace by lia.
    reflexivity.
Qed.

Lemma proof_of_uf_union_c_entail_wit_8 : uf_union_c_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength parent_pre n_pre (replace_Znth rx ry ps2_2)).
  Intros_p Hlen_replace.
  rewrite replace_Znth_Zlength in Hlen_replace.
  Exists ps2_2 rs2_2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH12 into Hsafe.
    unfold uf_union_after_rank_ry in Hsafe at 1.
    prog_nf in Hsafe.
    safe_choice_r Hsafe.
    safe_choice_l Hsafe.
    unfold write_parent in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_update' in Hsafe.
    refine (safeExec_conseq
              (equiv (uf_state_of n_pre (replace_Znth rx ry ps2_2) rs2_2))
              _ _ X_low_level_spec Hsafe _).
    intros s [s0 [Hs [_ Heq]]].
    subst s.
    cbv [equiv uf_state_equiv] in Heq |- *.
    subst s0.
    rewrite uf_state_of_set_parent_replace by lia.
    reflexivity.
Qed.

Lemma proof_of_uf_union_c_entail_wit_9 : uf_union_c_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps2_2 rs2_2.
  split_pure_spatial.
  - cancel.
  - rename PreH12 into Hsafe.
    split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    + dump_pre_spatial.
      pose proof Hsafe as Hsafe_bound.
      unfold uf_union_after_rank_ry in Hsafe_bound at 1.
      prog_nf in Hsafe_bound.
      safe_choice_r Hsafe_bound.
      safe_choice_r Hsafe_bound.
      unfold write_parent in Hsafe_bound at 1.
      prog_nf in Hsafe_bound.
      apply safeExec_assertS_seq in Hsafe_bound.
      apply safeExec_update'_bind in Hsafe_bound.
      unfold bump_rank in Hsafe_bound at 1.
      prog_nf in Hsafe_bound.
      apply safeExec_assertS_seq in Hsafe_bound.
      unfold safeExec, safe in Hsafe_bound.
      destruct Hsafe_bound as [s [[Hbump [s0 [Hs [_ Heq]]]] _]].
      subst s.
      cbv [equiv uf_state_equiv] in Heq.
      subst s0.
      unfold rank_bump_safe in Hbump.
      rewrite uf_rank_set_parent_state in Hbump.
      rewrite uf_size_set_parent_state in Hbump.
      destruct Hbump as [_ [_ Hbump_bound]].
      rewrite uf_state_of_rank_read in Hbump_bound by lia.
      simpl in Hbump_bound.
      rewrite PreH11.
      lia.
      lia.
    + prop_apply (IntArray.full_Zlength parent_pre n_pre (replace_Znth rx ry ps2_2)).
      Intros_p Hlen_replace.
      rewrite replace_Znth_Zlength in Hlen_replace.
      dump_pre_spatial.
      pose proof Hsafe as Hsafe_final.
      unfold uf_union_after_rank_ry in Hsafe_final at 1.
      prog_nf in Hsafe_final.
      safe_choice_r Hsafe_final.
      safe_choice_r Hsafe_final.
      unfold write_parent in Hsafe_final at 1.
      prog_nf in Hsafe_final.
      apply safeExec_assertS_seq in Hsafe_final.
      apply safeExec_update'_bind in Hsafe_final.
      refine (safeExec_conseq
                (equiv (uf_state_of n_pre (replace_Znth rx ry ps2_2) rs2_2))
                _ _ X_low_level_spec Hsafe_final _).
      intros s [s0 [Hs [_ Heq]]].
      subst s.
      cbv [equiv uf_state_equiv] in Heq |- *.
      subst s0.
      symmetry.
      rewrite uf_state_of_set_parent_replace by lia.
      reflexivity.
      lia.
Qed.

Lemma proof_of_uf_union_c_entail_wit_10 : uf_union_c_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength rank_pre n_pre (replace_Znth ry (ry_rank + 1) rs2_2)).
  Intros_p Hlen_replace.
  rewrite replace_Znth_Zlength in Hlen_replace.
  Exists ps2_2 rs2_2.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rename PreH9 into Hsafe.
    unfold bump_rank in Hsafe at 1.
    prog_nf in Hsafe.
    apply safeExec_assertS_seq in Hsafe.
    apply safeExec_update' in Hsafe.
    refine (safeExec_conseq
              (equiv (uf_state_of n_pre (replace_Znth rx ry ps2_2)
                         (replace_Znth ry (ry_rank + 1) rs2_2)))
              _ _ X_low_level_spec Hsafe _).
    intros s [s0 [Hs [_ Heq]]].
    subst s.
    cbv [equiv uf_state_equiv] in Heq |- *.
    subst s0.
    rewrite uf_state_of_inc_rank_replace by lia.
    rewrite PreH7.
    reflexivity.
Qed.

Lemma proof_of_uf_union_c_partial_solve_wit_2_pure : uf_union_c_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_uf_union_c_derive_high_level_spec_by_low_level_spec : uf_union_c_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps_high_level_spec rs_high_level_spec
    (fun r s =>
       (uf_union x_pre y_pre).(MonadErr.nrm)
         (uf_state_of n_pre ps_high_level_spec rs_high_level_spec) r s).
  split_pure_spatial.
  - cancel (IntArray.full parent_pre n_pre ps_high_level_spec).
    cancel (IntArray.full rank_pre n_pre rs_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros ps1_2 rs1_2.
    rename H6 into Hsafe_ret.
    pose proof (Hoare_safeexec_compose
                  (fun s =>
                     uf_abstract s repr_of_high_level_spec /\
                     valid s x_pre /\
                     valid s y_pre)
                  (uf_union x_pre y_pre)
                  (fun _ s =>
                     exists repr_of',
                       uf_abstract s repr_of' /\
                       merge (valid s) repr_of_high_level_spec x_pre y_pre repr_of')
                  (uf_union_correct x_pre y_pre repr_of_high_level_spec)
                  (equiv (uf_state_of n_pre ps1_2 rs1_2))
                  tt
                  (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)
                  Hsafe_ret) as Hcomp.
    assert (Hvalid_x : valid (uf_state_of n_pre ps_high_level_spec rs_high_level_spec) x_pre)
      by (unfold valid; simpl; lia).
    assert (Hvalid_y : valid (uf_state_of n_pre ps_high_level_spec rs_high_level_spec) y_pre)
      by (unfold valid; simpl; lia).
    destruct (Hcomp (conj H5 (conj Hvalid_x Hvalid_y)))
      as [sigma [[repr_of1 [Habs_sigma Hmerge_sigma]] Heq_sigma]].
    Exists ps1_2 rs1_2 repr_of1.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial.
        apply (uf_abstract_equiv sigma (uf_state_of n_pre ps1_2 rs1_2) repr_of1).
        -- symmetry; exact Heq_sigma.
        -- exact Habs_sigma.
      * dump_pre_spatial.
        apply (merge_valid_equiv sigma (uf_state_of n_pre ps1_2 rs1_2)
                 repr_of_high_level_spec x_pre y_pre repr_of1).
        -- symmetry; exact Heq_sigma.
        -- exact Hmerge_sigma.
  - split_pures; try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    assert (Hnoerr : ~ (uf_union x_pre y_pre).(MonadErr.err)
                        (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)).
    {
      destruct (uf_union_correct x_pre y_pre repr_of_high_level_spec) as [_ Herr].
      intro Herr_err.
      apply (Herr (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)).
      - split; [exact H5 | split; unfold valid; simpl; lia].
      - exact Herr_err.
    }
    unfold safeExec, safe.
    exists (uf_state_of n_pre ps_high_level_spec rs_high_level_spec).
    split.
    + reflexivity.
    + apply wp_self.
      exact Hnoerr.
Qed.

Lemma proof_of_uf_find_c_derive_low_level_spec_aux_by_low_level_spec : uf_find_c_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename H3 into Hsafe_bind.
  apply safeExec_bind in Hsafe_bind as (X_find & Hsafe_find & Hsafe_cont).
  Exists ps_low_level_spec_aux rs_low_level_spec_aux X_find.
  split_pure_spatial.
  - cancel (IntArray.full parent_pre n_pre ps_low_level_spec_aux).
    cancel (IntArray.full rank_pre n_pre rs_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros ps1_2 retval_2.
    Exists ps1_2 retval_2.
    split_pure_spatial.
    + cancel.
    + split_pures; try (dump_pre_spatial; assumption).
      dump_pre_spatial.
      apply Hsafe_cont.
      exact H5.
  - split_pures; try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_uf_find_c_derive_high_level_spec_by_low_level_spec : uf_find_c_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ps_high_level_spec rs_high_level_spec
    (fun r s =>
       (uf_find x_pre).(MonadErr.nrm)
         (uf_state_of n_pre ps_high_level_spec rs_high_level_spec) r s).
  split_pure_spatial.
  - cancel (IntArray.full parent_pre n_pre ps_high_level_spec).
    cancel (IntArray.full rank_pre n_pre rs_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros ps1_2 retval_2.
    rename H6 into Hsafe_ret.
    pose proof (Hoare_safeexec_compose
                  (fun s => uf_abstract s repr_of_high_level_spec /\ valid s x_pre)
                  (uf_find x_pre)
                  (fun y s =>
                     y = repr_of_high_level_spec x_pre /\
                     uf_abstract s repr_of_high_level_spec)
                  (uf_find_correct x_pre repr_of_high_level_spec)
                  (equiv (uf_state_of n_pre ps1_2 rs_high_level_spec))
                  retval_2
                  (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)
                  Hsafe_ret) as Hcomp.
    assert (Hvalid_x : valid (uf_state_of n_pre ps_high_level_spec rs_high_level_spec) x_pre)
      by (unfold valid; simpl; lia).
    destruct (Hcomp (conj H3 Hvalid_x)) as [sigma [[Hret Habs_sigma] Heq_sigma]].
    Exists ps1_2 retval_2.
    split_pure_spatial.
    + cancel.
    + split_pures; try (dump_pre_spatial; assumption).
      dump_pre_spatial.
      apply (uf_abstract_equiv sigma (uf_state_of n_pre ps1_2 rs_high_level_spec)
               repr_of_high_level_spec).
      * symmetry; exact Heq_sigma.
      * exact Habs_sigma.
  - split_pures; try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    assert (Hnoerr : ~ (uf_find x_pre).(MonadErr.err)
                        (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)).
    {
      destruct (uf_find_correct x_pre repr_of_high_level_spec) as [_ Herr].
      intro Herr_err.
      apply (Herr (uf_state_of n_pre ps_high_level_spec rs_high_level_spec)).
      - split; [exact H3 | unfold valid; simpl; lia].
      - exact Herr_err.
    }
    unfold safeExec, safe.
    exists (uf_state_of n_pre ps_high_level_spec rs_high_level_spec).
    split.
    + reflexivity.
    + apply wp_self.
      exact Hnoerr.
Qed.
