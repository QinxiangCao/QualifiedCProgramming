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
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_free_InequList_return_wit_1_split_goal_spatial :
  free_InequList_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  sep_apply (inequlist_0_implies_nil l n).
  Intros.
  cancel.
Qed.

Lemma proof_of_free_InequList_return_wit_1 : free_InequList_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_InequList_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_free_InequList_return_wit_3_split_goal_spatial :
  free_InequList_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  sep_apply (inequlist_0_implies_nil l0 n).
  Intros.
  cancel.
Qed.

Lemma proof_of_free_InequList_return_wit_3 : free_InequList_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_InequList_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_eliminate_entail_wit_1 : eliminate_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst retval retval_2 retval_3.
  Exists nil.
  Exists nil.
  Exists nil.
  Exists l_low_level_spec.
  Exists empty_bp.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    cancel (InequList r_pre n_low_level_spec l_low_level_spec).
    simpl.
    unfold NULL.
    cancel.
    repeat split_pure_spatial; try cancel; auto.
    split_pures.
    all: dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial. unfold form_BP, empty_bp; simpl; auto.
Qed.

Lemma proof_of_eliminate_entail_wit_2_1 : eliminate_entail_wit_2_1.
Proof.
  (LLM_pre_process ltac:(int_auto)); subst todo_2.
  Exists (x :: up_2). Exists lo_2. Exists re_2. Exists l0.
  Exists (add_upper x b_2).
  split_pure_spatial.
  - simpl; Exists h; Exists upper; split_pure_spatial.
    + cancel (mpz_coef_array h n_low_level_spec x).
      cancel (&( cur # "InequList" ->ₛ "coef") # Ptr |-> h).
      cancel (&( cur # "InequList" ->ₛ "next") # Ptr |-> upper).
      cancel (InequList upper n_low_level_spec up_2).
      cancel (InequList y n_low_level_spec l0).
      cancel (InequList lower n_low_level_spec lo_2).
      cancel (InequList remain n_low_level_spec re_2).
      cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      apply store_ptr_undef_store_ptr.
    + split_pures; dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; auto; lia].
    + match goal with
      | Hsafe : safeExec ATrue (eliminate_from num_pre _ _) _ |- _ =>
          unfold eliminate_from in Hsafe at 1; simpl in Hsafe;
          unfold eliminate_body in Hsafe at 1; prog_nf in Hsafe;
          safe_choice_l Hsafe;
          [dump_pre_spatial; exact Hsafe | rewrite <- coef_Znth_nth by lia; auto]
      end.
    + dump_pre_spatial.
      match goal with
      | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ =>
          unfold form_BP, add_upper in *; destruct Hform as [? [? ?]];
          subst; simpl; auto
      end.
Qed.

Lemma proof_of_eliminate_entail_wit_2_2 : eliminate_entail_wit_2_2.
Proof.
  (LLM_pre_process ltac:(int_auto)); subst todo_2.
  Exists up_2. Exists (x :: lo_2). Exists re_2. Exists l0.
  Exists (add_lower x b_2).
  split_pure_spatial.
  - simpl; Exists h; Exists lower; split_pure_spatial.
    + cancel (mpz_coef_array h n_low_level_spec x).
      cancel (&( cur # "InequList" ->ₛ "coef") # Ptr |-> h).
      cancel (&( cur # "InequList" ->ₛ "next") # Ptr |-> lower).
      cancel (InequList lower n_low_level_spec lo_2).
      cancel (InequList y n_low_level_spec l0).
      cancel (InequList upper n_low_level_spec up_2).
      cancel (InequList remain n_low_level_spec re_2).
      cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      apply store_ptr_undef_store_ptr.
    + split_pures; dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; auto; lia].
    + match goal with
      | Hsafe : safeExec ATrue (eliminate_from num_pre _ _) _ |- _ =>
          unfold eliminate_from in Hsafe at 1; simpl in Hsafe;
          unfold eliminate_body in Hsafe at 1; prog_nf in Hsafe;
          safe_choice_r Hsafe; safe_choice_l Hsafe;
          [dump_pre_spatial; exact Hsafe | rewrite <- coef_Znth_nth by lia; lia]
      end.
    + dump_pre_spatial.
      match goal with
      | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ =>
          unfold form_BP, add_lower in *; destruct Hform as [? [? ?]];
          subst; simpl; auto
      end.
Qed.

Lemma proof_of_eliminate_entail_wit_2_3 : eliminate_entail_wit_2_3.
Proof.
  (LLM_pre_process ltac:(int_auto)); subst todo_2.
  Exists up_2. Exists lo_2. Exists (x :: re_2). Exists l0.
  Exists (add_remain x b_2).
  split_pure_spatial.
  - simpl; Exists h; Exists remain; split_pure_spatial.
    + cancel (mpz_coef_array h n_low_level_spec x).
      cancel (&( cur # "InequList" ->ₛ "coef") # Ptr |-> h).
      cancel (&( cur # "InequList" ->ₛ "next") # Ptr |-> remain).
      cancel (InequList remain n_low_level_spec re_2).
      cancel (InequList y n_low_level_spec l0).
      cancel (InequList upper n_low_level_spec up_2).
      cancel (InequList lower n_low_level_spec lo_2).
      cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      apply store_ptr_undef_store_ptr.
    + split_pures; dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; auto; lia].
    + match goal with
      | Hsafe : safeExec ATrue (eliminate_from num_pre _ _) _ |- _ =>
          unfold eliminate_from in Hsafe at 1; simpl in Hsafe;
          unfold eliminate_body in Hsafe at 1; prog_nf in Hsafe;
          safe_choice_r Hsafe; safe_choice_r Hsafe;
          [dump_pre_spatial; exact Hsafe | rewrite <- coef_Znth_nth by lia; auto]
      end.
    + dump_pre_spatial.
      match goal with
      | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ =>
          unfold form_BP, add_remain in *; destruct Hform as [? [? ?]];
          subst; simpl; auto
      end.
Qed.

Lemma proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  Exists remain.
  Exists lower.
  Exists upper.
  Exists up_2.
  Exists lo_2.
  Exists re_2.
  Exists b_2.
  split_pure_spatial.
  - sep_apply (inequlist_0_implies_nil todo n_low_level_spec).
    Intros.
    subst.
    cancel.
  - sep_apply (inequlist_0_implies_nil todo n_low_level_spec).
    Intros.
    subst.
    unfold eliminate_from in PreH2 at 1.
    simpl in PreH2.
    split_pures; try solve [dump_pre_spatial; auto; try lia].
Qed.

Lemma proof_of_generate_new_constr_entail_wit_1 : generate_new_constr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists 0.
  Exists l.
  Exists (Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
                 (- coef_Znth cur_num_pre c2_low_level_spec 0)).
  Exists (- coef_Znth cur_num_pre c2_low_level_spec 0).
  Exists (coef_Znth cur_num_pre c1_low_level_spec 0).
  Exists ((- coef_Znth cur_num_pre c2_low_level_spec 0) ÷
          Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
               (- coef_Znth cur_num_pre c2_low_level_spec 0)).
  Exists (coef_Znth cur_num_pre c1_low_level_spec 0 ÷
          Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
               (- coef_Znth cur_num_pre c2_low_level_spec 0)).
  Exists (@nil Z).
  prop_apply (mpz_coef_array_length r1_pre (num_pre + 1) c1_low_level_spec).
  Intros.
  prop_apply (mpz_coef_array_length r2_pre (num_pre + 1) c2_low_level_spec).
  Intros.
  split_pure_spatial.
  - cancel (mpz_coef_array retval_7 (num_pre + 1) l).
    cancel (mpz_coef_array r1_pre (num_pre + 1) c1_low_level_spec).
    cancel (mpz_coef_array r2_pre (num_pre + 1) c2_low_level_spec).
    repeat cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; subst; auto; try lia].
    + dump_pre_spatial.
      match goal with
      | Hsafe : safeExec ATrue (generate_new_constr_prog _ _ _) _ |- _ =>
          unfold generate_new_constr_prog in Hsafe;
          safe_step Hsafe
      end.
      assert (Hgpos : 0 < Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
                 (- coef_Znth cur_num_pre c2_low_level_spec 0)).
      { pose proof (Z.gcd_nonneg (coef_Znth cur_num_pre c1_low_level_spec 0)
                     (- coef_Znth cur_num_pre c2_low_level_spec 0)).
        destruct (Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
                   (- coef_Znth cur_num_pre c2_low_level_spec 0)) eqn:Hg; try lia.
        apply Z.gcd_eq_0_l in Hg; lia. }
      rewrite zdiv_equiv by lia.
      rewrite zdiv_equiv by lia.
      match goal with
      | Hsafe : safeExec ATrue (generate_new_constr_from _ _ _ _ 0 nil) _ |- _ =>
          exact Hsafe
      end.
    + dump_pre_spatial. unfold coef_pre_eq. intros j Hj. lia.
  - unfold NULL. assumption.
  - unfold NULL. assumption.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (v := (m2_v_2 * coef_Znth i c2_low_level_spec 0 +
             m1_v_2 * coef_Znth i c1_low_level_spec 0)).
  Exists v.
  Exists (coef_replace_Znth i v c3_2).
  Exists g_v_2.
  Exists bn_v_2.
  Exists an_v_2.
  Exists m1_v_2.
  Exists m2_v_2.
  Exists (prefix_2 ++ v :: nil).
  subst v.
  split_pure_spatial.
  - repeat rewrite <- PreH10.
    repeat rewrite <- PreH3.
    repeat rewrite <- PreH4.
    repeat rewrite <- PreH5.
    repeat rewrite <- PreH6.
    repeat rewrite <- PreH7.
    change (store_Z (res + i * sizeof("__mpz_struct"))
        (m1_v_2 * coef_Znth i c1_low_level_spec 0 +
         m2_v_2 * coef_Znth i c2_low_level_spec 0))
      with (mpz_store res i
        (m1_v_2 * coef_Znth i c1_low_level_spec 0 +
         m2_v_2 * coef_Znth i c2_low_level_spec 0)).
    replace (m1_v_2 * coef_Znth i c1_low_level_spec 0 +
             m2_v_2 * coef_Znth i c2_low_level_spec 0)
      with (m2_v_2 * coef_Znth i c2_low_level_spec 0 +
            m1_v_2 * coef_Znth i c1_low_level_spec 0) by lia.
    sep_apply (mpz_coef_array_merge res i (num_pre + 1)
      (m2_v_2 * coef_Znth i c2_low_level_spec 0 +
       m1_v_2 * coef_Znth i c1_low_level_spec 0) c3_2);
      try lia; try assumption.
    cancel (mpz_coef_array r1_pre (num_pre + 1) c1_low_level_spec).
    cancel (mpz_coef_array r2_pre (num_pre + 1) c2_low_level_spec).
    cancel (mpz_coef_array res (num_pre + 1)
      (coef_replace_Znth i
        (m2_v_2 * coef_Znth i c2_low_level_spec 0 +
         m1_v_2 * coef_Znth i c1_low_level_spec 0) c3_2)).
    repeat cancel.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    + dump_pre_spatial.
      unfold generate_new_constr_from in PreH2.
      destruct (skipn (Z.to_nat i) (Constraint_list c1_low_level_spec)) as [|x0 xs] eqn:Hskip.
      { assert (Z.to_nat i < Datatypes.length (Constraint_list c1_low_level_spec))%nat as Hilt.
        { rewrite <- (Nat2Z.id (Datatypes.length (Constraint_list c1_low_level_spec))).
          apply Z2Nat.inj_lt; try lia.
          unfold coef_Zlength in PreH17.
          lia. }
        pose proof (proj2 (nth_error_Some (Constraint_list c1_low_level_spec) (Z.to_nat i)) Hilt)
          as Hsome.
        replace (Z.to_nat i) with (Z.to_nat i + 0)%nat in Hsome by lia.
        rewrite <- (@nth_error_skipn Z (Z.to_nat i) (Constraint_list c1_low_level_spec) 0%nat) in Hsome.
        rewrite Hskip in Hsome.
        simpl in Hsome.
        contradiction Hsome; reflexivity. }
      cbn in PreH2.
      prog_nf in PreH2.
      change (match Z.to_nat i with
              | 0%nat => const c1_low_level_spec
              | S m => nth m (coef c1_low_level_spec) 0
              end) with (coef_Znth i c1_low_level_spec 0) in PreH2.
      change (match Z.to_nat i with
              | 0%nat => const c2_low_level_spec
              | S m => nth m (coef c2_low_level_spec) 0
              end) with (coef_Znth i c2_low_level_spec 0) in PreH2.
      replace (m1_v_2 * coef_Znth i c1_low_level_spec 0 +
               m2_v_2 * coef_Znth i c2_low_level_spec 0)
        with (m2_v_2 * coef_Znth i c2_low_level_spec 0 +
              m1_v_2 * coef_Znth i c1_low_level_spec 0) in PreH2 by lia.
      unfold generate_new_constr_from.
      replace (skipn (Z.to_nat (i + 1)) (Constraint_list c1_low_level_spec)) with xs.
      2:{
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        assert (forall (A: Type) (n: nat) (l: list A),
          tl (skipn n l) = skipn (S n) l) as Htail.
        { intros A n.
          induction n; intros [|a l0]; simpl; auto. }
        pose proof (Htail Z (Z.to_nat i) (Constraint_list c1_low_level_spec)) as Htail_i.
        rewrite Hskip in Htail_i.
        simpl in Htail_i.
        exact Htail_i.
      }
      exact PreH2.
    + dump_pre_spatial. rewrite Zlength_app_cons. lia.
    + dump_pre_spatial. rewrite coef_replace_Znth_length. assumption.
    + dump_pre_spatial.
      eapply coef_pre_eq_extend; eauto; lia.
Qed.

Lemma proof_of_generate_new_constr_return_wit_1 : generate_new_constr_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists c3_2.
  split_pure_spatial.
  - cancel (mpz_coef_array r1_pre (num_pre + 1) c1_low_level_spec).
    cancel (mpz_coef_array r2_pre (num_pre + 1) c2_low_level_spec).
    cancel (mpz_coef_array res (num_pre + 1) c3_2).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      assert (Hi : i = num_pre + 1) by lia.
      assert (Heq : c3_2 = list_Constraint prefix).
      { eapply coef_pre_eq_complete; eauto. lia. }
      subst c3_2.
      unfold generate_new_constr_from in PreH2 at 1.
      assert (Hskip :
        skipn (Z.to_nat i) (Constraint_list c1_low_level_spec) = nil).
      { apply skipn_all2.
        apply Nat2Z.inj_le.
        rewrite Z2Nat.id by lia.
        unfold coef_Zlength in PreH17.
        lia. }
      rewrite Hskip in PreH2.
      cbn in PreH2.
      prog_nf in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_generate_new_constr_partial_solve_wit_16_pure : generate_new_constr_partial_solve_wit_16_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial; assumption.
  - dump_pre_spatial.
    match goal with
    | Hsafe : safeExec ATrue (generate_new_constr_prog _ _ _) _ |- _ =>
        unfold generate_new_constr_prog in Hsafe;
        safe_step Hsafe
    end.
    pose proof (gcd_divexact_pos
                  (coef_Znth cur_num_pre c1_low_level_spec 0)
                  (-(coef_Znth cur_num_pre c2_low_level_spec 0))
                  ltac:(lia) ltac:(lia)) as [Hg_nonzero [_ Hbn_div]].
    assert (Hg_pos : 0 < Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
                              (-(coef_Znth cur_num_pre c2_low_level_spec 0))).
    { pose proof (Z.gcd_nonneg (coef_Znth cur_num_pre c1_low_level_spec 0)
                                 (-(coef_Znth cur_num_pre c2_low_level_spec 0))).
      lia. }
    rewrite Z.quot_div_nonneg by lia.
    exact Hbn_div.
  - dump_pre_spatial.
    match goal with
    | Hsafe : safeExec ATrue (generate_new_constr_prog _ _ _) _ |- _ =>
        unfold generate_new_constr_prog in Hsafe;
        safe_step Hsafe
    end.
    pose proof (gcd_divexact_pos
                  (coef_Znth cur_num_pre c1_low_level_spec 0)
                  (-(coef_Znth cur_num_pre c2_low_level_spec 0))
                  ltac:(lia) ltac:(lia)) as [Hg_nonzero _].
    exact Hg_nonzero.
Qed.

Lemma proof_of_generate_new_constr_partial_solve_wit_17_pure : generate_new_constr_partial_solve_wit_17_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial; assumption.
  - dump_pre_spatial.
    match goal with
    | Hsafe : safeExec ATrue (generate_new_constr_prog _ _ _) _ |- _ =>
        unfold generate_new_constr_prog in Hsafe;
        safe_step Hsafe
    end.
    pose proof (gcd_divexact_pos
                  (coef_Znth cur_num_pre c1_low_level_spec 0)
                  (-(coef_Znth cur_num_pre c2_low_level_spec 0))
                  ltac:(lia) ltac:(lia)) as [Hg_nonzero [Han_div _]].
    assert (Hg_pos : 0 < Zgcd (coef_Znth cur_num_pre c1_low_level_spec 0)
                              (-(coef_Znth cur_num_pre c2_low_level_spec 0))).
    { pose proof (Z.gcd_nonneg (coef_Znth cur_num_pre c1_low_level_spec 0)
                                 (-(coef_Znth cur_num_pre c2_low_level_spec 0))).
      lia. }
    rewrite Z.quot_div_nonneg by lia.
    exact Han_div.
  - dump_pre_spatial.
    match goal with
    | Hsafe : safeExec ATrue (generate_new_constr_prog _ _ _) _ |- _ =>
        unfold generate_new_constr_prog in Hsafe;
        safe_step Hsafe
    end.
    pose proof (gcd_divexact_pos
                  (coef_Znth cur_num_pre c1_low_level_spec 0)
                  (-(coef_Znth cur_num_pre c2_low_level_spec 0))
                  ltac:(lia) ltac:(lia)) as [Hg_nonzero _].
    exact Hg_nonzero.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (@nil Constraint).
  Exists l1_low_level_spec.
  Exists l_init_low_level_spec.
  split_pure_spatial.
  - cancel (InequList r1_pre n_low_level_spec l1_low_level_spec).
    cancel (InequList r2_pre n_low_level_spec l2_low_level_spec).
    cancel (InequList init_pre n_low_level_spec l_init_low_level_spec).
    simpl.
    unfold NULL.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; auto; try lia].
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct l12_2 as [| c1_cur l12_tail].
  - simpl. Intros. contradiction.
  - simpl. Intros p1_coef p1_next.
    Exists (@nil Constraint). Exists l11_2. Exists (c1_cur :: l12_tail). Exists c1_cur.
    Exists l2_low_level_spec. Exists acc_2. Exists l12_tail.
    split_pure_spatial.
    + simpl.
      Exists p1_coef p1_next.
      split_pure_spatial.
      * cancel (InequList_seg r1_pre p1 n_low_level_spec l11_2).
        cancel (&( p1 # "InequList" ->ₛ "coef") # Ptr |-> p1_coef).
        cancel (mpz_coef_array p1_coef n_low_level_spec c1_cur).
        cancel (&( p1 # "InequList" ->ₛ "next") # Ptr |-> p1_next).
        cancel (InequList p1_next n_low_level_spec l12_tail).
        cancel (InequList r2_pre n_low_level_spec l2_low_level_spec).
        cancel (InequList res n_low_level_spec acc_2).
      * split_pures; dump_pre_spatial; subst; auto; try lia; try reflexivity.
    + split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l12_2.
  simpl. Intros p1_coef p1_next.
  destruct l22_2 as [| c2_cur l22_tail].
  - simpl. Intros. contradiction.
  - simpl. Intros p2_coef p2_next.
    Exists p2_next. Exists p1_next. Exists p2_coef. Exists p1_coef.
    Exists l21_2. Exists (c2_cur :: l22_tail). Exists l11_2. Exists (c1_cur_2 :: l12_tail_2).
    Exists c2_cur. Exists c1_cur_2. Exists l22_tail. Exists acc_2. Exists l12_tail_2.
    split_pure_spatial.
    + simpl.
      cancel (&( p1 # "InequList" ->ₛ "coef") # Ptr |-> p1_coef).
      cancel (&( p2 # "InequList" ->ₛ "coef") # Ptr |-> p2_coef).
      cancel (InequList_seg r1_pre p1 n_low_level_spec l11_2).
      cancel (mpz_coef_array p1_coef n_low_level_spec c1_cur_2).
      cancel (&( p1 # "InequList" ->ₛ "next") # Ptr |-> p1_next).
      cancel (InequList p1_next n_low_level_spec l12_tail_2).
      cancel (InequList_seg r2_pre p2 n_low_level_spec l21_2).
      cancel (mpz_coef_array p2_coef n_low_level_spec c2_cur).
      cancel (&( p2 # "InequList" ->ₛ "next") # Ptr |-> p2_next).
      cancel (InequList p2_next n_low_level_spec l22_tail).
      cancel (InequList res n_low_level_spec acc_2).
    + split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
      * dump_pre_spatial.
        unfold generate_new_constraints_inner_loop in PreH2 at 1.
        simpl in PreH2.
        prog_nf in PreH2.
        unfold generate_new_constraints_inner_body in PreH2 at 1.
        prog_nf in PreH2.
        exact PreH2.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst n_low_level_spec l1_low_level_spec l12_2 l2_low_level_spec l22_2.
  Exists (l21_2 ++ c2_cur :: nil). Exists l11_2. Exists (c1_cur_2 :: l12_tail_2).
  Exists c1_cur_2. Exists l22_tail. Exists (c3 :: acc_2). Exists l12_tail_2.
  split_pure_spatial.
  - sep_apply (InequList_seg_append l21_2 c2_cur (num_pre + 1) r2_pre p2 p2_next p2_coef PreH9 PreH11).
    cancel (InequList retval (num_pre + 1) (c3 :: acc_2)).
    simpl.
    Exists p1_coef p1_next.
    split_pure_spatial.
    + cancel (InequList_seg r1_pre p1 (num_pre + 1) l11_2).
      cancel (&( p1 # "InequList" ->ₛ "coef") # Ptr |-> p1_coef).
      cancel (mpz_coef_array p1_coef (num_pre + 1) c1_cur_2).
      cancel (&( p1 # "InequList" ->ₛ "next") # Ptr |-> p1_next).
      cancel (InequList p1_next (num_pre + 1) l12_tail_2).
      cancel (InequList_seg r2_pre p2_next (num_pre + 1) (l21_2 ++ c2_cur :: nil)).
      cancel (InequList p2_next (num_pre + 1) l22_tail).
    + split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
    dump_pre_spatial.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_5 : generate_new_constraint_list_entail_wit_5.
Proof.
  (LLM_pre_process ltac:(int_auto)); subst.
  inversion PreH6; subst; clear PreH6.
  Exists (l11_2 ++ c1_cur :: nil).
  Exists l12_tail.
  Exists acc_2.
  split_pure_spatial.
  - sep_apply (InequList_seg_append l11_2 c1_cur (num_pre + 1) r1_pre p1 y h PreH8 PreH1).
    sep_apply (InequList_seg_app l21 l22 (num_pre + 1) r2_pre 0).
    LLM_pre_process ltac:(int_auto).
  - sep_apply (inequlist_0_implies_nil l22 (num_pre + 1)).
    LLM_pre_process ltac:(int_auto).
    subst l22.
    simpl in PreH4.
    prog_nf in PreH4.
    rewrite app_nil_r in PreH4.
    rewrite app_nil_r.
    split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
    * dump_pre_spatial.
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p1. subst l1_low_level_spec. subst n_low_level_spec.
  Exists acc. split_pure_spatial.
  - sep_apply (InequList_seg_app l11 l12 (num_pre + 1) r1_pre 0).
    cancel (InequList r1_pre (num_pre + 1) (l11 ++ l12)).
    cancel (InequList r2_pre (num_pre + 1) l2_low_level_spec).
    cancel (InequList res (num_pre + 1) acc).
  - split_pures.
    + sep_apply (inequlist_0_implies_nil l12 (num_pre + 1)).
      Intros.
      subst l12.
      unfold generate_new_constraint_list_loop in PreH2 at 1.
      prog_nf in PreH2.
      dump_pre_spatial.
      exact PreH2.
Qed.

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_1_pure_split_goal_1 :
  generate_new_constraint_list_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_1_pure :
  generate_new_constraint_list_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply
    proof_of_generate_new_constraint_list_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l1_low_level_spec.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p1_low_level_spec).
    cancel (InequList p1_low_level_spec (n_pre + 1) l1_low_level_spec).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "upper")) FET_ptr BP0_upper).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "lower")) FET_ptr BP0_lower).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "remain")) FET_ptr BP0_remain).
    cbn.
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
  - split_pures; try solve [dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l3.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p1_low_level_spec).
    cancel (InequList retval (n_pre + 1) l3).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "upper")) FET_ptr BP0_upper).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "lower")) FET_ptr BP0_lower).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "remain")) FET_ptr BP0_remain).
    cbn.
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
  - split_pures; try solve [dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l3.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p1_low_level_spec).
    cancel (InequList retval (n_pre + 1) l3).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "upper")) FET_ptr BP0_upper).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "lower")) FET_ptr BP0_lower).
    sep_apply (poly_store_poly_undef_store (&( BP0 # "BoundPair" ->ₛ "remain")) FET_ptr BP0_remain).
    cbn.
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
  - split_pures; try solve [dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst BP0_lower; subst BP0_remain.
  Exists 0.
  Exists lo.
  split_pure_spatial.
  - sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "upper")) BP0_upper).
    sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "lower")) 0).
    sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "remain")) 0).
    cancel ( &( "BP0") # Ptr |-> BP0 ).
    cancel (pr_pre # Ptr |-> 0).
    cancel (InequList 0 (n_pre + 1) lo).
    cancel ( &( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_ ).
    cancel ( &( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_ ).
    cancel ( &( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_ ).
    sep_apply (inequlist_0_implies_nil re (n_pre + 1)).
    Intros.
    normalize.
    cancel.
  - split_pures.
    + sep_apply (inequlist_0_implies_nil lo (n_pre + 1)).
      Intros.
      sep_apply (inequlist_0_implies_nil re (n_pre + 1)).
      Intros.
      subst lo; subst re.
      dump_pre_spatial.
      unfold form_BP in PreH7.
      destruct PreH7 as [Hup [Hlo Hre]].
      unfold applyf in PreH5.
      unfold real_shadow_after_eliminate in PreH5.
      rewrite <- Hlo in PreH5.
      rewrite <- Hre in PreH5.
      unfold generate_new_constraint_list_prog in PreH5.
      rewrite generate_new_constraint_list_loop_nil_lower in PreH5.
      prog_nf in PreH5.
      unfold real_shadow_after_generate in PreH5.
      eapply (real_shadow_loop_nil_safeExec (cnt - 1)); [lia | exact PreH5].
Qed.

Lemma proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst BP0_upper; subst BP0_remain.
  Exists 0.
  Exists up.
  split_pure_spatial.
  - sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "upper")) 0).
    sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "lower")) BP0_lower).
    sep_apply (store_ptr_undef_store_ptr (&( BP0 # "BoundPair" ->ₛ "remain")) 0).
    cancel ( &( "BP0") # Ptr |-> BP0 ).
    cancel (pr_pre # Ptr |-> 0).
    cancel (InequList 0 (n_pre + 1) up).
    cancel ( &( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_ ).
    cancel ( &( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_ ).
    cancel ( &( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_ ).
    sep_apply (inequlist_0_implies_nil re (n_pre + 1)).
    Intros.
    normalize.
    cancel.
  - split_pures.
    + sep_apply (inequlist_0_implies_nil up (n_pre + 1)).
      Intros.
      sep_apply (inequlist_0_implies_nil re (n_pre + 1)).
      Intros.
      subst up; subst re.
      dump_pre_spatial.
      unfold form_BP in PreH5.
      destruct PreH5 as [Hup [Hlo Hre]].
      unfold applyf in PreH3.
      unfold real_shadow_after_eliminate in PreH3.
      rewrite <- Hup in PreH3.
      rewrite <- Hre in PreH3.
      unfold generate_new_constraint_list_prog in PreH3.
      simpl in PreH3.
      prog_nf in PreH3.
      unfold real_shadow_after_generate in PreH3.
      eapply (real_shadow_loop_nil_safeExec (cnt - 1)); [lia | exact PreH3].
Qed.

Lemma proof_of_real_shadow_return_wit_3 : real_shadow_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists r.
  Exists l.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold real_shadow_loop_prog in PreH2 at 1.
      unfold_loop in PreH2.
      unfold real_shadow_loop_body in PreH2 at 1.
      prog_nf in PreH2.
      safe_choice_r PreH2.
      unfold break in PreH2.
      prog_nf in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_real_shadow_partial_solve_wit_1_pure : real_shadow_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
  - eapply safeExec_proequiv with (c1 := real_shadow_loop_prog cnt l).
    + apply real_shadow_loop_step_equiv; lia.
    + exact PreH2.
  - apply real_shadow_loop_step_equiv; lia.
Qed.

Lemma proof_of_real_shadow_partial_solve_wit_4_pure : real_shadow_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (eliminate_pos_neg l b cnt PreH4 ltac:(lia) up lo re PreH5) as [Hpos Hneg].
  destruct PreH5 as [Hup [Hlo Hre]].
  subst up lo re.
  split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_real_shadow_partial_solve_wit_5_pure : real_shadow_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (eliminate_pos_neg l b cnt PreH6 ltac:(lia) up lo re PreH7) as [Hpos Hneg].
  destruct PreH7 as [Hup [Hlo Hre]].
  subst up lo re.
  split_pures; dump_pre_spatial; try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_lia_deduction_entail_wit_1 : lia_deduction_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2. Exists (@nil Constraint). Exists l2_2. Exists l2_2.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p2).
    cancel (InequList p2 (n_pre + 1) l2_2).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    simpl.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; auto.
  - repeat split_pures; try solve [dump_pre_spatial; subst; auto; try lia; try reflexivity].
Qed.

Lemma proof_of_lia_deduction_entail_wit_2 : lia_deduction_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2_2. Exists l2_2.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p2_2).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    sep_apply (InequList_seg_append_list l_done l0 x (n_pre + 1) p2_2 p y h PreH6 PreH4).
    rewrite PreH8, PreH5.
    cancel (InequList p2_2 (n_pre + 1) (l_done ++ x :: l0)).
  - split_pures.
    all: try solve [dump_pre_spatial; assumption || lia].
    dump_pre_spatial.
    assert (Hscan_true :
      forall todo,
        safeExec ATrue
          (found' <- list_iter lia_deduction_check_body todo true;;
           lia_deduction_after_check l2_2 found') X_low_level_spec ->
        safeExec ATrue (return (makepair 1 l2_2)) X_low_level_spec).
    {
      intro todo.
      induction todo as [| c todo IH]; intro Hscan.
      - simpl in Hscan.
        prog_nf in Hscan.
        unfold lia_deduction_after_check in Hscan at 1.
        prog_nf in Hscan.
        safe_choice_l Hscan.
        exact Hscan.
      - simpl in Hscan.
        unfold lia_deduction_check_body in Hscan at 1.
        prog_nf in Hscan.
        safe_choice_l Hscan.
        eapply IH.
        exact Hscan.
    }
    rewrite PreH5 in PreH7.
    unfold lia_deduction_scan_from_false in PreH7 at 1.
    unfold lia_deduction_scan_from in PreH7 at 1.
    simpl in PreH7.
    unfold lia_deduction_check_body in PreH7 at 1.
    prog_nf in PreH7.
    safe_choice_r PreH7.
    safe_choice_l PreH7.
    eapply Hscan_true.
    exact PreH7.
Qed.

Lemma proof_of_lia_deduction_entail_wit_3_1 : lia_deduction_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2_2. Exists (l_done_2 ++ x :: nil). Exists l2_2. Exists l0.
  split_pure_spatial.
  - sep_apply (InequList_seg_append l_done_2 x (n_pre + 1) p2_2 p y h);
      try easy.
    cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial.
      rewrite PreH5 in PreH7.
      unfold lia_deduction_scan_from_false in PreH7 at 1.
      unfold lia_deduction_scan_from in PreH7 at 1.
      simpl in PreH7.
      prog_nf in PreH7.
      unfold lia_deduction_check_body in PreH7 at 1.
      prog_nf in PreH7.
      safe_choice_r PreH7.
      safe_choice_r PreH7.
      all: try solve [
        unfold lia_deduction_scan_from_false;
        unfold lia_deduction_scan_from;
        exact PreH7
      ].
      all: try solve [lia].
      all: try solve [reflexivity].
    + dump_pre_spatial.
      rewrite PreH8, PreH5.
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_lia_deduction_entail_wit_3_2 : lia_deduction_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2_2. Exists (l_done_2 ++ x :: nil). Exists l2_2. Exists l0.
  split_pure_spatial.
  - sep_apply (InequList_seg_append l_done_2 x (n_pre + 1) p2_2 p y h);
      try easy.
    cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial.
      rewrite PreH5 in PreH7.
      unfold lia_deduction_scan_from_false in PreH7 at 1.
      unfold lia_deduction_scan_from in PreH7 at 1.
      simpl in PreH7.
      prog_nf in PreH7.
      unfold lia_deduction_check_body in PreH7 at 1.
      prog_nf in PreH7.
      safe_choice_r PreH7.
      safe_choice_r PreH7.
      all: try solve [
        unfold lia_deduction_scan_from_false;
        unfold lia_deduction_scan_from;
        exact PreH7
      ].
      all: try solve [lia].
      all: try solve [reflexivity].
    + dump_pre_spatial.
      rewrite PreH8, PreH5.
      rewrite <- app_assoc.
      reflexivity.
Qed.

Lemma proof_of_lia_deduction_return_wit_1 : lia_deduction_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2_3. Exists l2_3.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p2_3).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    rewrite PreH3.
    apply InequList_seg_app.
  - repeat split_pures.
    + dump_pre_spatial; auto.
    + rewrite PreH1.
      sep_apply (inequlist_0_implies_nil l_todo (n_pre + 1)).
      Intros.
      dump_pre_spatial.
      match goal with
      | Hnil : l_todo = nil |- _ => rewrite Hnil in PreH2
      | Hnil : nil = l_todo |- _ => rewrite <- Hnil in PreH2
      end.
      unfold lia_deduction_scan_from_false in PreH2 at 1.
      unfold lia_deduction_scan_from in PreH2 at 1.
      simpl in PreH2.
      prog_nf in PreH2.
      unfold lia_deduction_after_check in PreH2 at 1.
      prog_nf in PreH2.
      safe_choice_r PreH2.
      exact PreH2.
Qed.

Lemma proof_of_lia_deduction_return_wit_2 : lia_deduction_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists p2_3. Exists l2_3.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (pr_pre # Ptr |-> p2_3).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_lia_deduction_partial_solve_wit_1_pure_split_goal_1 :
  lia_deduction_partial_solve_wit_1_pure_split_goal_1.
Proof.
  unfold lia_deduction_partial_solve_wit_1_pure_split_goal_1.
  intros.
  dump_pre_spatial.
  unfold lia_deduction_prog.
  unfold lia_deduction_check_prog.
  unfold lia_deduction_after_real_shadow.
  unfold lia_deduction_scan_from_false.
  unfold lia_deduction_scan_from.
  unfold lia_deduction_after_check.
  reflexivity.
Qed.

Lemma proof_of_lia_deduction_partial_solve_wit_1_pure_split_goal_2 :
  lia_deduction_partial_solve_wit_1_pure_split_goal_2.
Proof.
  unfold lia_deduction_partial_solve_wit_1_pure_split_goal_2.
  intros.
  dump_pre_spatial.
  unfold lia_deduction_prog.
  unfold lia_deduction_check_prog.
  unfold lia_deduction_after_real_shadow.
  unfold lia_deduction_scan_from_false.
  unfold lia_deduction_scan_from.
  unfold lia_deduction_after_check.
  reflexivity.
Qed.

Lemma proof_of_lia_deduction_partial_solve_wit_1_pure : lia_deduction_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lia_deduction_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_lia_deduction_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_lia_deduction_derive_low_level_spec_aux_by_low_level_spec : lia_deduction_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros BP0_remain. Intros BP0_lower. Intros BP0_upper.
  prop_apply (InequList_coef_Zlength
    p1_low_level_spec_aux (n_pre + 1) l1_low_level_spec_aux).
  Intros_p Hcoef_lengths.
  pose proof (proof_of_lia_deduction_triple
    n_pre l1_low_level_spec_aux) as Htriple.
  assert (Hpre :
    1 <= n_pre /\
    (forall c : Constraint,
      In c l1_low_level_spec_aux -> coef_Zlength c = n_pre + 1)).
  { split; [lia | exact Hcoef_lengths]. }
  assert (Herr_free :
    ~ MonadErr.err (lia_deduction_prog n_pre l1_low_level_spec_aux) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists p1_low_level_spec_aux.
  Exists l1_low_level_spec_aux.
  Exists (fun r x =>
    (lia_deduction_prog n_pre l1_low_level_spec_aux).(MonadErr.nrm)
      tt r x).
  Exists BP0.
  Exists BP0_remain. Exists BP0_lower. Exists BP0_upper.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain).
    cancel (pr_pre # Ptr |-> p1_low_level_spec_aux).
    cancel (InequList p1_low_level_spec_aux (n_pre + 1) l1_low_level_spec_aux).
    apply_sepcon_adjoint.
    cancel.
    Split.
    + 
      Intros p2_3. Intros l2_3. Intros retval_2. Intros. Intros.
      Left.
      Exists p2_3. Exists l2_3. Exists retval_2.
      split_pure_spatial.
      * cancel (&( "BP0") # Ptr |-> BP0).
        cancel (pr_pre # Ptr |-> p2_3).
        cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      * split_pures.
        -- dump_pre_spatial; auto.
        -- dump_pre_spatial.
           match goal with
           | Hret : safeExec ATrue (return (makepair 1 l2_3)) _ |- _ =>
               apply safeExec_ret_Atrue_finnal in Hret;
               destruct Hret as [σ Hrun]
           end.
           unfold applyf.
           eapply (highstepbind_derive
             (lia_deduction_prog n_pre l1_low_level_spec_aux)
             c_low_level_spec_aux ATrue (makepair 1 l2_3) ATrue).
           ++ apply (proj2 (hs_eval_equiv_angelic_triple
                (lia_deduction_prog n_pre l1_low_level_spec_aux)
                ATrue (makepair 1 l2_3) ATrue)).
              unfold valid_angelic_triple, ATrue.
              intros [] _.
              exists (makepair 1 l2_3), σ.
              split; [exact Hrun | auto].
           ++ exact H.
    + 
      Intros p2_4. Intros l2_4. Intros retval_2. Intros. Intros.
      Right.
      Exists p2_4. Exists l2_4. Exists retval_2.
      split_pure_spatial.
      * cancel (&( "BP0") # Ptr |-> BP0).
        cancel (pr_pre # Ptr |-> p2_4).
        cancel (InequList p2_4 (n_pre + 1) l2_4).
        cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      * split_pures.
        -- dump_pre_spatial; auto.
        -- dump_pre_spatial.
           match goal with
           | Hret : safeExec ATrue (return (makepair 0 l2_4)) _ |- _ =>
               apply safeExec_ret_Atrue_finnal in Hret;
               destruct Hret as [σ Hrun]
           end.
           unfold applyf.
           eapply (highstepbind_derive
             (lia_deduction_prog n_pre l1_low_level_spec_aux)
             c_low_level_spec_aux ATrue (makepair 0 l2_4) ATrue).
           ++ apply (proj2 (hs_eval_equiv_angelic_triple
                (lia_deduction_prog n_pre l1_low_level_spec_aux)
                ATrue (makepair 0 l2_4) ATrue)).
              unfold valid_angelic_triple, ATrue.
              intros [] _.
              exists (makepair 0 l2_4), σ.
              split; [exact Hrun | auto].
           ++ exact H.
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_lia_deduction_derive_high_level_spec_by_low_level_spec : lia_deduction_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros BP0_remain. Intros BP0_lower. Intros BP0_upper. Intros BP0.
  prop_apply (InequList_coef_Zlength p1_high_level_spec (n_pre + 1) l1_high_level_spec).
  Intros_p Hcoef_lengths.
  pose proof (proof_of_lia_deduction_triple n_pre l1_high_level_spec) as Htriple.
  assert (Hpre : 1 <= n_pre /\ (forall c : Constraint, In c l1_high_level_spec -> coef_Zlength c = n_pre + 1)) by (split; [lia | exact Hcoef_lengths]).
  assert (Herr_free : ~ MonadErr.err (lia_deduction_prog n_pre l1_high_level_spec) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists p1_high_level_spec.
  Exists l1_high_level_spec.
  Exists (fun r x => (lia_deduction_prog n_pre l1_high_level_spec).(MonadErr.nrm) tt r x).
  Exists BP0.
  Exists BP0_remain. Exists BP0_lower. Exists BP0_upper.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain).
    cancel (pr_pre # Ptr |-> p1_high_level_spec).
    cancel (InequList p1_high_level_spec (n_pre + 1) l1_high_level_spec).
    apply_sepcon_adjoint.
    cancel.
    Split.
    + Intros p2_3. Intros l2_2. Intros retval_2. Intros. Intros.
      match goal with
      | Hsafe : safeExec ATrue (return (makepair 1 l2_2)) _ |- _ =>
          apply safeExec_ret_Atrue_finnal in Hsafe;
          destruct Hsafe as [σ Hrun]
      end.
      unfold Hoare in Htriple.
      destruct Htriple as [Hpost _].
      specialize (Hpost (makepair 1 l2_2) tt σ Hpre Hrun).
      simpl in Hpost.
      destruct Hpost as [[Hret Hunsat] | [Hret [Himpl Hzero]]]; [| lia].
      Left.
      Exists BP0. Exists p2_3. Exists retval_2.
      split_pure_spatial.
      * cancel (pr_pre # Ptr |-> p2_3).
        cancel (&( "BP0") # Ptr |-> BP0).
        cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      * split_pures.
        -- dump_pre_spatial; auto.
        -- dump_pre_spatial; auto.
    + Intros p2_4. Intros l2_3. Intros retval_2. Intros. Intros.
      match goal with
      | Hsafe : safeExec ATrue (return (makepair 0 l2_3)) _ |- _ =>
          apply safeExec_ret_Atrue_finnal in Hsafe;
          destruct Hsafe as [σ Hrun]
      end.
      unfold Hoare in Htriple.
      destruct Htriple as [Hpost _].
      specialize (Hpost (makepair 0 l2_3) tt σ Hpre Hrun).
      simpl in Hpost.
      destruct Hpost as [[Hret Hunsat] | [Hret [Himpl Hzero]]]; [lia |].
      Right.
      Exists BP0. Exists p2_4. Exists l2_3. Exists retval_2.
      split_pure_spatial.
      * cancel (pr_pre # Ptr |-> p2_4).
        cancel (InequList p2_4 (n_pre + 1) l2_3).
        cancel (&( "BP0") # Ptr |-> BP0).
        cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
        cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
      * split_pures.
        -- dump_pre_spatial; auto.
        -- dump_pre_spatial; auto.
        -- dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_real_shadow_derive_low_level_spec_aux_by_low_level_spec : real_shadow_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros BP0_remain. Intros BP0_lower. Intros BP0_upper.
  prop_apply (InequList_coef_Zlength p1_low_level_spec_aux (n_pre + 1) l1_low_level_spec_aux).
  Intros_p Hcoef_lengths.
  pose proof (proof_of_real_shadow_triple n_pre l1_low_level_spec_aux) as Htriple.
  assert (Hpre :
    1 <= n_pre /\
    (forall c : Constraint,
      In c l1_low_level_spec_aux -> coef_Zlength c = n_pre + 1)).
  { split; [lia | exact Hcoef_lengths]. }
  assert (Herr_free :
    ~ MonadErr.err (real_shadow_prog n_pre l1_low_level_spec_aux) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists p1_low_level_spec_aux.
  Exists l1_low_level_spec_aux.
  Exists (fun l x =>
    (real_shadow_prog n_pre l1_low_level_spec_aux).(MonadErr.nrm) tt l x).
  Exists BP0.
  Exists BP0_remain. Exists BP0_lower. Exists BP0_upper.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain).
    cancel (pr_pre # Ptr |-> p1_low_level_spec_aux).
    cancel (InequList p1_low_level_spec_aux (n_pre + 1) l1_low_level_spec_aux).
    apply_sepcon_adjoint.
    cancel.
    Intros p2_2. Intros l2_2. Intros. Intros.
    match goal with
    | Hsafe : safeExec ATrue (return l2_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    assert (Hcont_safe :
      safeExec ATrue
        (applyf c_low_level_spec_aux l2_2)
        X_low_level_spec_aux).
    {
      unfold applyf.
      eapply (highstepbind_derive
        (real_shadow_prog n_pre l1_low_level_spec_aux)
        c_low_level_spec_aux ATrue l2_2 ATrue).
      - apply (proj2 (hs_eval_equiv_angelic_triple
          (real_shadow_prog n_pre l1_low_level_spec_aux)
          ATrue l2_2 ATrue)).
        unfold valid_angelic_triple, ATrue.
        intros [] _.
        exists l2_2, σ.
        split; [exact Hrun | auto].
      - exact H.
    }
    Exists p2_2. Exists l2_2.
    split_pure_spatial.
    * cancel (&( "BP0") # Ptr |-> BP0).
      cancel (pr_pre # Ptr |-> p2_2).
      cancel (InequList p2_2 (n_pre + 1) l2_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    * dump_pre_spatial.
      exact Hcont_safe.
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_real_shadow_derive_high_level_spec_by_low_level_spec : real_shadow_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros BP0_remain. Intros BP0_lower. Intros BP0_upper.
  prop_apply (InequList_coef_Zlength p1_high_level_spec (n_pre + 1) l1_high_level_spec).
  Intros_p Hcoef_lengths.
  pose proof (proof_of_real_shadow_triple n_pre l1_high_level_spec) as Htriple.
  assert (Hpre : 1 <= n_pre /\ (forall c : Constraint, In c l1_high_level_spec -> coef_Zlength c = n_pre + 1)) by (split; [lia | exact Hcoef_lengths]).
  assert (Herr_free : ~ MonadErr.err (real_shadow_prog n_pre l1_high_level_spec) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists p1_high_level_spec.
  Exists l1_high_level_spec.
  Exists (fun l x => (real_shadow_prog n_pre l1_high_level_spec).(MonadErr.nrm) tt l x).
  Exists BP0.
  Exists BP0_remain. Exists BP0_lower. Exists BP0_upper.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain).
    cancel (pr_pre # Ptr |-> p1_high_level_spec).
    cancel (InequList p1_high_level_spec (n_pre + 1) l1_high_level_spec).
    apply_sepcon_adjoint.
    cancel.
    Intros p2_2. Intros l2_2. Intros. Intros.
    match goal with
    | Hsafe : safeExec ATrue (return l2_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
    specialize (Hpost l2_2 tt σ Hpre Hrun).
    destruct Hpost as [Himpl [Hzero Hlen]].
    Exists p2_2. Exists l2_2.
    split_pure_spatial.
    + cancel (&( "BP0") # Ptr |-> BP0).
      cancel (pr_pre # Ptr |-> p2_2).
      cancel (InequList p2_2 (n_pre + 1) l2_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    + split_pures.
      * dump_pre_spatial; auto.
      * dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_generate_new_constraint_list_derive_low_level_spec_aux_with_rel_by_low_level_spec : generate_new_constraint_list_derive_low_level_spec_aux_with_rel_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (InequList_coef_Zlength r1_pre n_low_level_spec_aux_with_rel l1_low_level_spec_aux_with_rel).
  prop_apply (InequList_coef_Zlength r2_pre n_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel).
  Intros_p Hlen_r1.
  Intros_p Hlen_r2.
  pose proof (proof_of_generate_new_constraint_list_triple
                cur_num_pre
                l1_low_level_spec_aux_with_rel
                l2_low_level_spec_aux_with_rel
                l_init_low_level_spec_aux_with_rel) as Htriple.
  assert (Hpair :
    forall c1 c2 : Constraint,
      In c1 l1_low_level_spec_aux_with_rel ->
      In c2 l2_low_level_spec_aux_with_rel ->
      1 <= cur_num_pre /\
      cur_num_pre < coef_Zlength c1 /\
      coef_Zlength c1 = coef_Zlength c2 /\
      coef_Znth cur_num_pre c1 0 > 0 /\
      coef_Znth cur_num_pre c2 0 < 0).
  {
    intros c1 c2 Hc1 Hc2.
    repeat split; try lia.
    - pose proof (Hlen_r1 c1 Hc1); lia.
    - rewrite (Hlen_r1 c1 Hc1), (Hlen_r2 c2 Hc2); reflexivity.
    - exact (H4 c1 Hc1).
    - exact (H5 c2 Hc2).
  }
  assert (Herr_free : ~ MonadErr.err (generate_new_constraint_list_prog
    cur_num_pre l1_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel
    l_init_low_level_spec_aux_with_rel) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists n_low_level_spec_aux_with_rel.
  Exists l1_low_level_spec_aux_with_rel.
  Exists l2_low_level_spec_aux_with_rel.
  Exists l_init_low_level_spec_aux_with_rel.
  Exists (fun l x => (generate_new_constraint_list_prog
    cur_num_pre l1_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel
    l_init_low_level_spec_aux_with_rel).(MonadErr.nrm) tt l x).
  split_pure_spatial.
  - cancel (InequList r1_pre n_low_level_spec_aux_with_rel l1_low_level_spec_aux_with_rel).
    cancel (InequList r2_pre n_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel).
    cancel (InequList init_pre n_low_level_spec_aux_with_rel l_init_low_level_spec_aux_with_rel).
    apply_sepcon_adjoint.
    cancel.
    Intros l3_2.
    Intros retval_addr.
    Intros.
    match goal with
    | Hsafe : safeExec ATrue (return l3_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
        specialize (Hpost l3_2 tt σ Hpair Hrun).
        destruct Hpost as [l4 [Hgen Heq]].
        assert (Hcont_safe : safeExec ATrue
          (applyf c_low_level_spec_aux_with_rel l3_2)
          X_low_level_spec_aux_with_rel).
        {
          unfold applyf.
          eapply (highstepbind_derive
            (generate_new_constraint_list_prog
              cur_num_pre
              l1_low_level_spec_aux_with_rel
              l2_low_level_spec_aux_with_rel
              l_init_low_level_spec_aux_with_rel)
            c_low_level_spec_aux_with_rel ATrue l3_2 ATrue).
          - apply (proj2 (hs_eval_equiv_angelic_triple
              (generate_new_constraint_list_prog
                cur_num_pre
                l1_low_level_spec_aux_with_rel
                l2_low_level_spec_aux_with_rel
                l_init_low_level_spec_aux_with_rel)
              ATrue l3_2 ATrue)).
            unfold valid_angelic_triple, ATrue.
            intros [] _.
            exists l3_2, σ.
            split; [exact Hrun | auto].
          - exact H.
        }
        Exists l4.
        Exists l3_2.
        Exists retval_addr.
        split_pure_spatial.
        + cancel (InequList r1_pre n_low_level_spec_aux_with_rel l1_low_level_spec_aux_with_rel).
          cancel (InequList r2_pre n_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel).
          cancel (InequList retval_addr n_low_level_spec_aux_with_rel l3_2).
        + split_pures; try solve [dump_pre_spatial; auto].
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_generate_new_constraint_list_derive_high_level_spec_by_low_level_spec : generate_new_constraint_list_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (InequList_coef_Zlength r1_pre n_high_level_spec l1_high_level_spec).
  prop_apply (InequList_coef_Zlength r2_pre n_high_level_spec l2_high_level_spec).
  Intros_p Hlen_r1.
  Intros_p Hlen_r2.
  pose proof (proof_of_generate_new_constraint_list_triple cur_num_pre l1_high_level_spec l2_high_level_spec l_init_high_level_spec) as Htriple.
  assert (Hpair :
    forall c1 c2 : Constraint,
      In c1 l1_high_level_spec ->
      In c2 l2_high_level_spec ->
      1 <= cur_num_pre /\
      cur_num_pre < coef_Zlength c1 /\
      coef_Zlength c1 = coef_Zlength c2 /\
      coef_Znth cur_num_pre c1 0 > 0 /\
      coef_Znth cur_num_pre c2 0 < 0).
  {
    intros c1 c2 Hc1 Hc2.
    pose proof (H3 c1 Hc1) as Hpos.
    pose proof (H4 c2 Hc2) as Hneg.
    pose proof (Hlen_r1 c1 Hc1) as Hlen1.
    pose proof (Hlen_r2 c2 Hc2) as Hlen2.
    repeat split; try lia.
  }
  assert (Herr_free : ~ MonadErr.err (generate_new_constraint_list_prog cur_num_pre l1_high_level_spec l2_high_level_spec l_init_high_level_spec) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists n_high_level_spec.
  Exists l1_high_level_spec.
  Exists l2_high_level_spec.
  Exists l_init_high_level_spec.
  Exists (fun l x => (generate_new_constraint_list_prog cur_num_pre l1_high_level_spec l2_high_level_spec l_init_high_level_spec).(MonadErr.nrm) tt l x).
  split_pure_spatial.
  - cancel (InequList r1_pre n_high_level_spec l1_high_level_spec).
    cancel (InequList r2_pre n_high_level_spec l2_high_level_spec).
    cancel (InequList init_pre n_high_level_spec l_init_high_level_spec).
    apply_sepcon_adjoint.
    cancel.
    Intros l3_2.
    Intros retval_2.
    Intros.
    match goal with
    | Hsafe : safeExec ATrue (return l3_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
        specialize (Hpost l3_2 tt σ Hpair Hrun).
        destruct Hpost as [l4 [Hgen Hl3]].
        Exists l3_2.
        Exists l4.
        Exists retval_2.
        split_pure_spatial.
        + cancel (InequList r1_pre n_high_level_spec l1_high_level_spec).
          cancel (InequList r2_pre n_high_level_spec l2_high_level_spec).
          cancel (InequList retval_2 n_high_level_spec l3_2).
        + split_pures; dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_generate_new_constr_derive_low_level_spec_aux_by_low_level_spec : generate_new_constr_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hexec : safeExec ATrue
      (bind (generate_new_constr_prog _ _ _) _) _ |- _ =>
      pose proof Hexec as Hguards
  end.
  unfold generate_new_constr_prog in Hguards at 1.
  prog_nf in Hguards.
  safe_step Hguards.
  assert (Hr1_nonnull : r1_pre <> NULL) by exact H3.
  assert (Hr2_nonnull : r2_pre <> NULL) by exact H4.
  prop_apply (mpz_coef_array_length
    r1_pre (num_pre + 1) c1_low_level_spec_aux Hr1_nonnull).
  prop_apply (mpz_coef_array_length
    r2_pre (num_pre + 1) c2_low_level_spec_aux Hr2_nonnull).
  Intros_p Hlen_r1.
  Intros_p Hlen_r2.
  pose proof (proof_of_generate_new_constr_triple
    cur_num_pre c1_low_level_spec_aux c2_low_level_spec_aux) as Htriple.
  assert (Hpre :
    1 <= cur_num_pre /\
    cur_num_pre < coef_Zlength c1_low_level_spec_aux /\
    coef_Zlength c1_low_level_spec_aux =
      coef_Zlength c2_low_level_spec_aux /\
    coef_Znth cur_num_pre c1_low_level_spec_aux 0 > 0 /\
    coef_Znth cur_num_pre c2_low_level_spec_aux 0 < 0).
  { repeat split; try lia. }
  assert (Herr_free :
    ~ MonadErr.err
      (generate_new_constr_prog
        cur_num_pre c1_low_level_spec_aux c2_low_level_spec_aux) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists c1_low_level_spec_aux.
  Exists c2_low_level_spec_aux.
  Exists (fun c x =>
    (generate_new_constr_prog
      cur_num_pre c1_low_level_spec_aux c2_low_level_spec_aux).(MonadErr.nrm)
      tt c x).
  split_pure_spatial.
  - cancel (mpz_coef_array r1_pre (num_pre + 1) c1_low_level_spec_aux).
    cancel (mpz_coef_array r2_pre (num_pre + 1) c2_low_level_spec_aux).
    apply_sepcon_adjoint.
    Intros c3_2.
    Intros retval_2.
    Intros. Intros.
    match goal with
    | Hsafe : safeExec ATrue (return c3_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    assert (Hcont_safe :
      safeExec ATrue
        (applyf c_low_level_spec_aux c3_2)
        X_low_level_spec_aux).
    {
      unfold applyf.
      eapply (highstepbind_derive
        (generate_new_constr_prog
          cur_num_pre c1_low_level_spec_aux c2_low_level_spec_aux)
        c_low_level_spec_aux ATrue c3_2 ATrue).
      - apply (proj2 (hs_eval_equiv_angelic_triple
          (generate_new_constr_prog
            cur_num_pre c1_low_level_spec_aux c2_low_level_spec_aux)
          ATrue c3_2 ATrue)).
        unfold valid_angelic_triple, ATrue.
        intros [] _.
        exists c3_2, σ.
        split; [exact Hrun | auto].
      - exact H.
    }
    Exists c3_2.
    Exists retval_2.
    split_pure_spatial.
    + cancel (mpz_coef_array r1_pre (num_pre + 1) c1_low_level_spec_aux).
      cancel (mpz_coef_array r2_pre (num_pre + 1) c2_low_level_spec_aux).
      cancel (mpz_coef_array retval_2 (num_pre + 1) c3_2).
    + split_pures.
      * dump_pre_spatial; auto.
      * dump_pre_spatial.
        exact Hcont_safe.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_generate_new_constr_derive_high_level_spec_by_low_level_spec : generate_new_constr_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hr1_nonnull : r1_pre <> NULL) by exact H2.
  assert (Hr2_nonnull : r2_pre <> NULL) by exact H3.
  prop_apply (mpz_coef_array_length r1_pre (num_pre + 1) c1_high_level_spec Hr1_nonnull).
  prop_apply (mpz_coef_array_length r2_pre (num_pre + 1) c2_high_level_spec Hr2_nonnull).
  Intros_p Hlen_r1.
  Intros_p Hlen_r2.
  pose proof (proof_of_generate_new_constr_triple cur_num_pre c1_high_level_spec c2_high_level_spec) as Htriple.
  assert (Hpre :
    1 <= cur_num_pre /\
    cur_num_pre < coef_Zlength c1_high_level_spec /\
    coef_Zlength c1_high_level_spec = coef_Zlength c2_high_level_spec /\
    coef_Znth cur_num_pre c1_high_level_spec 0 > 0 /\
    coef_Znth cur_num_pre c2_high_level_spec 0 < 0).
  { repeat split; try lia. }
  assert (Herr_free : ~ MonadErr.err (generate_new_constr_prog cur_num_pre c1_high_level_spec c2_high_level_spec) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; eauto.
  }
  Exists c1_high_level_spec.
  Exists c2_high_level_spec.
  Exists (fun c x => (generate_new_constr_prog cur_num_pre c1_high_level_spec c2_high_level_spec).(MonadErr.nrm) tt c x).
  split_pure_spatial.
  - cancel (mpz_coef_array r1_pre (num_pre + 1) c1_high_level_spec).
    cancel (mpz_coef_array r2_pre (num_pre + 1) c2_high_level_spec).
    apply_sepcon_adjoint.
    cancel.
    Intros c3_2.
    Intros retval_2.
    Intros. Intros.
    match goal with
    | Hsafe : safeExec ATrue (return c3_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
        specialize (Hpost c3_2 tt σ Hpre Hrun).
        Exists c3_2.
        Exists retval_2.
        split_pure_spatial.
        + cancel (mpz_coef_array r1_pre (num_pre + 1) c1_high_level_spec).
          cancel (mpz_coef_array r2_pre (num_pre + 1) c2_high_level_spec).
          cancel (mpz_coef_array retval_2 (num_pre + 1) c3_2).
        + split_pures; dump_pre_spatial; auto.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_eliminate_derive_low_level_spec_aux_with_rel_by_low_level_spec : eliminate_derive_low_level_spec_aux_with_rel_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (proof_of_eliminate_prog_triple num_pre l_low_level_spec_aux_with_rel) as Htriple.
  assert (Herr_free : ~ MonadErr.err (eliminate_prog num_pre l_low_level_spec_aux_with_rel) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; [exact I | exact Herrun].
  }
  Exists n_low_level_spec_aux_with_rel.
  Exists l_low_level_spec_aux_with_rel.
  Exists (fun b x => (eliminate_prog num_pre l_low_level_spec_aux_with_rel).(MonadErr.nrm) tt b x).
  Exists BP0.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    cancel (InequList r_pre n_low_level_spec_aux_with_rel l_low_level_spec_aux_with_rel).
    apply_sepcon_adjoint.
    Intros BP0_remain_2.
    Intros BP0_lower_2.
    Intros BP0_upper_2.
    Intros up_2.
    Intros lo_2.
    Intros re_2.
    Intros b_2.
    Intros.
    match goal with
    | Hsafe : safeExec ATrue (return b_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
    specialize (Hpost b_2 tt σ I Hrun).
    assert (Hcont_safe :
      safeExec ATrue
        (applyf c_low_level_spec_aux_with_rel b_2)
        X_low_level_spec_aux_with_rel).
    {
      unfold applyf.
      eapply (highstepbind_derive
        (eliminate_prog num_pre l_low_level_spec_aux_with_rel)
        c_low_level_spec_aux_with_rel ATrue b_2 ATrue).
      - apply (proj2 (hs_eval_equiv_angelic_triple
          (eliminate_prog num_pre l_low_level_spec_aux_with_rel)
          ATrue b_2 ATrue)).
        unfold valid_angelic_triple, ATrue.
        intros [] _.
        exists b_2, σ.
        split; [exact Hrun | auto].
      - exact H.
    }
    Exists BP0_remain_2.
    Exists BP0_lower_2.
    Exists BP0_upper_2.
    Exists up_2.
    Exists lo_2.
    Exists re_2.
    Exists b_2.
    split_pure_spatial.
    + cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper_2).
      cancel (InequList BP0_upper_2 n_low_level_spec_aux_with_rel up_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower_2).
      cancel (InequList BP0_lower_2 n_low_level_spec_aux_with_rel lo_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain_2).
      cancel (InequList BP0_remain_2 n_low_level_spec_aux_with_rel re_2).
    + split_pures.
      * dump_pre_spatial.
        exact Hcont_safe.
      * dump_pre_spatial.
        exact Hpost.
      * dump_pre_spatial.
        match goal with
        | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ => exact Hform
        end.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_eliminate_derive_low_level_spec_aux_by_low_level_spec : eliminate_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (proof_of_eliminate_prog_triple num_pre l_low_level_spec_aux) as Htriple.
  assert (Herr_free :
    ~ MonadErr.err (eliminate_prog num_pre l_low_level_spec_aux) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; [exact I | exact Herrun].
  }
  Exists n_low_level_spec_aux.
  Exists l_low_level_spec_aux.
  Exists (fun b x =>
    (eliminate_prog num_pre l_low_level_spec_aux).(MonadErr.nrm) tt b x).
  Exists BP0.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    cancel (InequList r_pre n_low_level_spec_aux l_low_level_spec_aux).
    apply_sepcon_adjoint.
    Intros BP0_remain_2.
    Intros BP0_lower_2.
    Intros BP0_upper_2.
    Intros up_2.
    Intros lo_2.
    Intros re_2.
    Intros b_2.
    Intros.
    match goal with
    | Hsafe : safeExec ATrue (return b_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    assert (Hcont_safe :
      safeExec ATrue
        (applyf c_low_level_spec_aux b_2)
        X_low_level_spec_aux).
    {
      unfold applyf.
      eapply (highstepbind_derive
        (eliminate_prog num_pre l_low_level_spec_aux)
        c_low_level_spec_aux ATrue b_2 ATrue).
      - apply (proj2 (hs_eval_equiv_angelic_triple
          (eliminate_prog num_pre l_low_level_spec_aux)
          ATrue b_2 ATrue)).
        unfold valid_angelic_triple, ATrue.
        intros [] _.
        exists b_2, σ.
        split; [exact Hrun | auto].
      - exact H.
    }
    Exists BP0_remain_2.
    Exists BP0_lower_2.
    Exists BP0_upper_2.
    Exists up_2.
    Exists lo_2.
    Exists re_2.
    Exists b_2.
    split_pure_spatial.
    + cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper_2).
      cancel (InequList BP0_upper_2 n_low_level_spec_aux up_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower_2).
      cancel (InequList BP0_lower_2 n_low_level_spec_aux lo_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain_2).
      cancel (InequList BP0_remain_2 n_low_level_spec_aux re_2).
    + split_pures.
      * dump_pre_spatial.
        exact Hcont_safe.
      * dump_pre_spatial.
        match goal with
        | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ => exact Hform
        end.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.

Lemma proof_of_eliminate_derive_high_level_spec_by_low_level_spec : eliminate_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (proof_of_eliminate_prog_triple num_pre l_high_level_spec) as Htriple.
  assert (Herr_free : ~ MonadErr.err (eliminate_prog num_pre l_high_level_spec) tt).
  {
    unfold Hoare in Htriple.
    destruct Htriple as [_ Herr].
    intro Herrun.
    eapply Herr; [exact I | exact Herrun].
  }
  Exists n_high_level_spec.
  Exists l_high_level_spec.
  Exists (fun b x => (eliminate_prog num_pre l_high_level_spec).(MonadErr.nrm) tt b x).
  Exists BP0.
  split_pure_spatial.
  - cancel (&( "BP0") # Ptr |-> BP0).
    cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |->_).
    cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |->_).
    cancel (InequList r_pre n_high_level_spec l_high_level_spec).
    apply_sepcon_adjoint.
    Intros BP0_remain_2.
    Intros BP0_lower_2.
    Intros BP0_upper_2.
    Intros up_2.
    Intros lo_2.
    Intros re_2.
    Intros b_2.
    Intros.
    match goal with
    | Hsafe : safeExec ATrue (return b_2) _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hsafe;
        destruct Hsafe as [σ Hrun]
    end.
    unfold Hoare in Htriple.
    destruct Htriple as [Hpost _].
    specialize (Hpost b_2 tt σ I Hrun).
    Exists BP0_remain_2.
    Exists BP0_lower_2.
    Exists BP0_upper_2.
    Exists up_2.
    Exists lo_2.
    Exists re_2.
    Exists b_2.
    split_pure_spatial.
    + cancel (&( "BP0") # Ptr |-> BP0).
      cancel (&( BP0 # "BoundPair" ->ₛ "upper") # Ptr |-> BP0_upper_2).
      cancel (InequList BP0_upper_2 n_high_level_spec up_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "lower") # Ptr |-> BP0_lower_2).
      cancel (InequList BP0_lower_2 n_high_level_spec lo_2).
      cancel (&( BP0 # "BoundPair" ->ₛ "remain") # Ptr |-> BP0_remain_2).
      cancel (InequList BP0_remain_2 n_high_level_spec re_2).
    + split_pures.
      * dump_pre_spatial.
        exact Hpost.
      * dump_pre_spatial.
        match goal with
        | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ => exact Hform
        end.
      * dump_pre_spatial.
        match goal with
        | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ =>
            pose proof (eliminate_pos_neg l_high_level_spec b_2 num_pre
              Hpost ltac:(lia) up_2 lo_2 re_2 Hform) as [Hpos _]
        end.
        exact Hpos.
      * dump_pre_spatial.
        match goal with
        | Hform : form_BP up_2 lo_2 re_2 b_2 |- _ =>
            pose proof (eliminate_pos_neg l_high_level_spec b_2 num_pre
              Hpost ltac:(lia) up_2 lo_2 re_2 Hform) as [_ Hneg]
        end.
        exact Hneg.
  - split_pures; try solve [dump_pre_spatial; subst; auto; try lia].
    dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    exact Herr_free.
Qed.
