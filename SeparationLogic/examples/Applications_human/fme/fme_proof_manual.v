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
From SimpleC.EE.Applications_human.fme Require Import fme_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.fme Require Import fme_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Proof.
  pre_process.
  entailer!.
  rewrite <- Z.gcd_comm in PreH1.
  rewrite Z.gcd_rem in PreH1.
  - rewrite Z.gcd_comm. auto.
  - auto.
Qed.

Lemma proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Proof.
  pre_process.
  entailer!.
  rewrite PreH1.
  rewrite Z.gcd_0_r_nonneg.
  - reflexivity.
  - lia.
Qed.

Lemma proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Proof. 
  pre_process.
  entailer!.
  - apply Z.rem_nonneg; lia.
  - apply Z.le_trans with a_pre.
    + apply Z.rem_le; lia.
    + lia.
Qed.

Lemma proof_of_free_InequList_return_wit_1 : free_InequList_return_wit_1.
Proof.
  pre_process. subst.
  sep_apply inequlist_0_implies_nil.
  entailer!.
Qed.

Lemma proof_of_free_InequList_return_wit_3 : free_InequList_return_wit_3.
Proof.
  pre_process. subst.
  sep_apply inequlist_0_implies_nil.
  entailer!.
Qed.

Lemma proof_of_eliminate_entail_wit_2 : eliminate_entail_wit_2.
Proof.
  pre_process.
  Exists nil nil nil.
  Exists {| upper := nil; lower := nil; remain := nil |}.
  Exists nil l.
  entailer!; simpl.
  - entailer!.
  - unfold form_BP. tauto.
  - split; intros; simpl; tauto.
Qed.

Lemma proof_of_eliminate_entail_wit_3_3 : eliminate_entail_wit_3_3.
Proof.
  pre_process.
  set (re := x::re_2) in *.
  Exists up_2 lo_2 re.
  Exists {| upper := up_2; lower := lo_2; remain := re|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef remain. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_re l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x as Hstep.
    apply Hstep; try tauto.
    lia.
  - subst l.
    subst l2_2.
    unfold l1.
    apply list_split_adjust.
Qed.

(* similar to wit_3_1 *)
Lemma proof_of_eliminate_entail_wit_3_2 : eliminate_entail_wit_3_2.
Proof.
  pre_process.
  set (lo := x::lo_2) in *.
  Exists up_2 lo re_2.
  Exists {| upper := up_2; lower := lo; remain := re_2|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef lower. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_lo l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x as Hstep.
    apply Hstep; try tauto; try lia.
  - subst l.
    subst l2_2.
    unfold l1.
    apply list_split_adjust.
Qed.

Lemma proof_of_eliminate_entail_wit_3_1 : eliminate_entail_wit_3_1.
Proof.
  pre_process.
  set (up := x::up_2) in *.
  Exists up lo_2 re_2.
  Exists {| upper := up; lower := lo_2; remain := re_2|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef upper. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_up l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x as Helim_step.
    apply Helim_step; try tauto; try lia.
  - rewrite PreH6, PreH3.
    unfold l1.
    apply list_split_adjust. 
Qed.

Lemma proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Proof.
  pre_process.
  Exists remain lower upper.
  Exists up_2 lo_2 re_2 bp.
  Intros.
  rewrite PreH1.
  sep_apply inequlist_0_implies_nil.
  Intros.
  rewrite H in PreH2; clear H.
  rewrite app_nil_r in PreH2.
  rewrite PreH2 in *; clear PreH2.
  entailer!;
  induction PreH3;
  destruct PreH4 as [BP1 [BP2 BP3]];
  rewrite <- BP1 in elim_upper;
  rewrite <- BP2 in elim_lower;
  rewrite <- BP3 in elim_remain;
  clear BP1 BP2 BP3.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply PreH14.
    specialize elim_remain with c.
    tauto.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply PreH14.
    specialize elim_lower with c.
    tauto.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply PreH14.
    specialize elim_upper with c.
    tauto.
  - unfold InequList_nth_neg.
    intros.
    rewrite elim_lower in H.
    destruct H.
    rewrite coef_Znth_nth; try lia.
    split; try lia.
    unfold LP_abs_in_int_range in PreH14.
    specialize PreH14 with c.
    apply PreH14 in H.
    unfold abs_in_int_range in H.
    specialize H with num_pre.
    rewrite coef_Znth_nth in H; lia.
  - unfold InequList_nth_pos.
    intros.
    rewrite elim_upper in H.
    destruct H.
    rewrite coef_Znth_nth; try lia.
    split; try lia.
    unfold LP_abs_in_int_range in PreH14.
    specialize PreH14 with c.
    apply PreH14 in H.
    unfold abs_in_int_range in H.
    specialize H with num_pre.
    rewrite coef_Znth_nth in H; lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_2 : generate_new_constr_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  assert (retval = 0 \/ retval <> 0) as Hretval_cases by lia.
  destruct Hretval_cases as [Hretval0 | Hretval_nonzero].
  + rewrite Hretval0 in PreH1.
    symmetry in PreH1.
    apply Z.gcd_eq_0_l in PreH1.
    lia.
  + lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_3 : generate_new_constr_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  assert (retval = 0 \/ retval <> 0) as Hretval_cases by lia.
  destruct Hretval_cases as [Hretval0 | Hretval_nonzero].
  + rewrite Hretval0 in PreH1.
    symmetry in PreH1.
    apply Z.gcd_eq_0_l in PreH1.
    lia.
  + lia.
Qed.  

Lemma proof_of_generate_new_constr_safety_wit_4 : generate_new_constr_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (- coef_Znth cur_num_pre c2 0 ÷ retval > 0).
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
  + lia.
Qed. 

Lemma proof_of_generate_new_constr_safety_wit_6 : generate_new_constr_safety_wit_6.
Proof.
  pre_process.
  assert (- coef_Znth cur_num_pre c2 0 ÷ retval > 0).
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
  + entailer!.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_9 : generate_new_constr_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  assert (coef_Znth cur_num_pre c1 0 ÷ retval > 0).
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_11 : generate_new_constr_safety_wit_11.
Proof.
  pre_process.
  assert (coef_Znth cur_num_pre c1 0 ÷ retval > 0).
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + entailer!.
Qed. 

Lemma proof_of_generate_new_constr_safety_wit_24 : generate_new_constr_safety_wit_24.
Proof.
  pre_process.
  unfold in_int_range in PreH7.
  entailer!.
  + pose proof PreH7 i.
    lia.
  + pose proof PreH7 i.
    lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_25 : generate_new_constr_safety_wit_25.
Proof.
  pre_process.
  unfold in_int_range in PreH6.
  entailer!.
  + pose proof PreH6 i.
    lia.
  + pose proof PreH6 i.
    lia.
Qed. 

Lemma proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Proof.
  pre_process.
  entailer! ; subst m1v m2v ; try lia.
  + unfold in_int_range.
    intros.
    lia.
  + unfold in_int_range.
    intros.
    lia.
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_3 : generate_new_constr_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  + unfold in_int_range.
    unfold in_int_range in PreH15.
    intros.
    assert (i0 < i \/ i0 >= i) as Hi_cases by lia.
    destruct Hi_cases.
    - apply PreH15.
      lia.
    - assert (i0 = i) as Hi_eq by lia.
      rewrite Hi_eq.
      assert (m2v * lb2 <= m2v * coef_Znth i c2 0 <= m2v * ub2) by nia.
      assert (-INT_MAX <= m2v * lb2 /\ m2v * ub2 <= INT_MAX).
      * split.
        ++ rewrite PreH13. apply Zquot.Z_mult_quot_ge. lia.
        ++ rewrite PreH12. apply Zquot.Z_mult_quot_le. lia.
      * lia.
  + unfold in_int_range.
    unfold in_int_range in PreH14.
    intros.
    assert (i0 < i \/ i0 >= i) as Hi_cases by lia.
    destruct Hi_cases.
    - apply PreH14.
      lia.
    - assert (i0 = i) as Hi_eq by lia.
      rewrite Hi_eq.
      assert (m1v * lb1 <= m1v * coef_Znth i c1 0 <= m1v * ub1) by nia.
      assert (-INT_MAX <= m1v * lb1 /\ m1v * ub1 <= INT_MAX).
      * split.
        ++ rewrite PreH11. apply Zquot.Z_mult_quot_ge. lia.
        ++ rewrite PreH10. apply Zquot.Z_mult_quot_le. lia.
      * lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_4 : generate_new_constr_entail_wit_4.
Proof.
  pre_process.
  Exists l.
  prop_apply (coef_array_length r1_pre).
  prop_apply (coef_array_length r2_pre).
  entailer!.
  + unfold generate_new_constraint_partial.
    split ; [ | split ; [ | split]] ; try auto.
    - assert (m1v * coef_Znth cur_num_pre c1 0 = m2v * (- coef_Znth cur_num_pre c2 0)).
      {
        subst m1v m2v.
        assert (retval > 0). {
          subst retval.
          pose proof Z.gcd_nonneg (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0).
          destruct (Z.eq_dec (Z.gcd (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0)) 0).
          + apply Z.gcd_eq_0_l in e. lia.
          + lia.
        }
        subst retval.
        repeat rewrite zdiv_equiv ; try lia.
        rewrite Z.gcd_comm.
        rewrite Z.gcd_div_swap.
        lia.
      }
      lia.
    - intros. lia.
  + assert (i = num_pre + 1) as Hi by lia.
    rewrite Hi in PreH13.
    apply PreH13.
  + assert (i = num_pre + 1) as Hi by lia.
    rewrite Hi in PreH12.
    apply PreH12.
  + unfold NULL ; lia. 
  + unfold NULL ; lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_5 : generate_new_constr_entail_wit_5.
Proof.
  pre_process.
  destruct (Z.eq_dec i_2 0).
  {
    sep_apply IntArray.missing_i_merge_to_full; try lia.
    subst i_2.
    unfold coef_array at 5.
    unfold Constraint_list.
    Exists ({| const := (m2v * coef_Znth 0 c2 0 +
    m1v * coef_Znth 0 c1 0) ; coef := coef c3_2|}). simpl. 
    unfold replace_Znth. simpl. 
    Right. entailer!.
    * unfold abs_in_int_range. intros.
      unfold coef_Znth, Constraint_list. simpl.
      unfold abs_in_int_range, coef_Znth, Constraint_list in PreH14 ; simpl in PreH14.
      unfold coef_Znth, Constraint_list in PreH4, PreH3 ; simpl in PreH4, PreH3.
      destruct (Z.eq_dec i0 0).
      - subst. unfold Znth in *. simpl in *. lia.
      - specialize (PreH14 i0 (ltac:(lia))).
        unfold Znth in PreH14. unfold Znth.
        simpl. destruct (Zto_nat i0) eqn : En; try lia.
        simpl in PreH14. lia.  
    * unfold generate_new_constraint_partial.
      split ; [ | split ; [ | split]] ; try auto.
      - assert (m1v * coef_Znth cur_num_pre c1 0 = m2v * (- coef_Znth cur_num_pre c2 0)).
        {
          subst m1v m2v.
          assert (retval > 0). {
            subst retval.
            pose proof Z.gcd_nonneg (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0).
            destruct (Z.eq_dec (Z.gcd (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0)) 0).
            + apply Z.gcd_eq_0_l in e. lia.
            + lia.
          }
          subst retval.
          repeat rewrite zdiv_equiv ; try lia.
          rewrite Z.gcd_comm.
          rewrite Z.gcd_div_swap.
          lia.
        }
        lia.
      - intros. 
        assert (i0 = 0) by lia. subst.
        unfold coef_Znth, Constraint_list in PreH4, PreH3 ; simpl in PreH4, PreH3.
        unfold coef_Znth, Constraint_list. simpl.
        unfold Znth in * ; simpl in * ; lia.
  }
  {
    Exists (coef_replace_Znth i_2 (m2v * coef_Znth i_2 c2 0 + m1v * coef_Znth i_2 c1 0) c3_2).
    sep_apply coef_array_merge ; try (unfold NULL ; lia).
    prop_apply (coef_array_length res) ; try lia .
    entailer!.
    * unfold abs_in_int_range.
      intros.
      assert (i0 = i_2 \/ i0 < i_2 \/ i0 > i_2) as Hcase by lia.
      destruct Hcase as [Hi | Hcase].
      + rewrite Hi.
        rewrite coef_replace_Znth_eq. lia.
        lia.
      + destruct Hcase as [Hlt | Hgt].
        - rewrite coef_replace_Znth_le.
          ++ unfold abs_in_int_range in PreH14.
            pose proof PreH14 i0.
            lia.
          ++ lia.
        - rewrite coef_replace_Znth_ge.
          ++ unfold abs_in_int_range in PreH14.
            pose proof PreH14 i0.
            lia.
          ++ lia.
    * unfold generate_new_constraint_partial.
      unfold generate_new_constraint_partial in PreH12.
      destruct PreH12 as [Hmul [Hrange [Hbase Hstep]]].
      split ; [ | split ; [ | split]] ; try auto.
      intros.
      assert (i0 < i_2 \/ i0 >= i_2) as Hcase by lia.
      destruct Hcase as [Hlt | Hge].
      + assert (coef_Znth i0 c3_2 0 = m1v * coef_Znth i0 c1 0 + m2v * coef_Znth i0 c2 0) as Hcoef.
        - apply Hstep. lia.
        - rewrite <-Hcoef. 
          apply coef_replace_Znth_le.
          lia.
      + assert (i0 = i_2) as Hi by lia.
        rewrite Hi.
        assert (m1v * coef_Znth i_2 c1 0 + m2v * coef_Znth i_2 c2 0 =
                m2v * coef_Znth i_2 c2 0 + m1v * coef_Znth i_2 c1 0) as Hcomm by lia.
        rewrite Hcomm.
        apply coef_replace_Znth_eq.
        lia.
  }
Qed. 

Lemma proof_of_generate_new_constr_return_wit_1 : generate_new_constr_return_wit_1.
Proof.  
  pre_process.
  prop_apply (coef_array_length r2_pre). 
  Exists c3_2. Intros.
  prop_apply (coef_array_length r1_pre).
  prop_apply (coef_array_length res).
  entailer!.
  all : try (unfold NULL ; lia).
  apply generate_new_constraint_complete ; try lia.
  exists (num_pre + 1), m1v, m2v.
  split ; [ lia | split ; [lia | split ; [lia | ]]].
  assert (num_pre + 1 = i_2) as Hi by lia.
  rewrite Hi.
  apply PreH8.
Qed.

Lemma proof_of_generate_new_constr_partial_solve_wit_11_pure : generate_new_constr_partial_solve_wit_11_pure.
Proof.
  pre_process.
  assert (Hi_range: 0 <= i /\ i < num_pre + 1) by lia.
  unfold in_int_range in PreH6, PreH7.
  pose proof (PreH6 i Hi_range) as [Hr1lo Hr1hi].
  pose proof (PreH7 i Hi_range) as [Hr2lo Hr2hi].
  entailer!; lia.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Proof.
  pre_process.
  Exists l_init nil nil l1.
  entailer!.
  + unfold InequList_seg.
    entailer!.
  + unfold generate_new_constraints.
    intros.
    tauto.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Proof.
  pre_process.
  Exists p1_next_2.
  Exists p1_coef.
  Exists l3 l4.
  Exists nil l2.
  Exists l11 x l13.
  entailer!.
  + unfold InequList_seg.
    entailer!.
  + unfold generate_new_constraints_partial.
    destruct l12.
    - exists l4, nil.
      split.
      * intros.
        unfold In.
        tauto.
      * split.
        ++ apply PreH10.
        ++ intros Hin.
           intros Hin_nil; inversion Hin_nil.
    - exists l4, nil.
      split.
      * intros.
        split; try tauto.
        unfold In. tauto.
      * split.
        ++ apply PreH10.
        ++ intros Hin.
           intros Hin_nil; inversion Hin_nil.
  + rewrite PreH9.
    rewrite PreH1.
    auto.
Qed. 

Lemma proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Proof.
  pre_process.
  Exists p1_next_2 p1_coef_3.
  Exists (c3 :: l3_3).
  Exists (c3 :: l4_3).
  Exists (l21_2 ++ x_2 :: nil) l23.
  Exists l11_3 x1_2 l12_3.
  entailer!.
  + {
    entailer!.
    rewrite <- PreH8.
    sep_apply (InequList_seg_append l21_2 x_2 n r2_pre p2 p2_next p2_coef).
    2: { unfold NULL; lia. }
    2: { unfold NULL; lia. }
    entailer!.
  }
  + unfold LP_abs_in_int_range.
    intros c Hin.
    destruct Hin as [Heq | Hin].
    - rewrite <- Heq.
      rewrite PreH8.
      auto.
    - unfold LP_abs_in_int_range in PreH18.
      apply PreH18.
      auto.
  + rewrite PreH17.
    simpl.
    reflexivity.
  + apply generate_new_constraints_step.
    split.
    - rewrite <- PreH5; auto.
    - apply PreH3.
  + rewrite <-list_split_adjust.
    rewrite <- PreH5. auto.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Proof. 
  pre_process.
  Exists l3_3 l4_3.
  Exists (l11_3 ++ x1 :: nil) l12_3.
  rewrite PreH1.
  sep_apply (inequlist_0_implies_nil l22).
  entailer!.
  + sep_apply InequList_seg_append; try easy.
    entailer!.
    sep_apply InequList_seg_degeneration.
    rewrite PreH8.
    rewrite H.
    rewrite app_nil_r.
    entailer!.
  + apply generate_new_constraints_complete.
    rewrite PreH8.
    subst l22.
    rewrite app_nil_r.
    auto.
  + rewrite <-list_split_adjust.
    auto.
Qed. 

Lemma proof_of_generate_new_constraint_list_return_wit_2 : generate_new_constraint_list_return_wit_2.
Proof.
  pre_process.
  Left.
  rewrite <- PreH6.
  entailer!.
  sep_apply (InequList_seg_append_list l11_2); try easy.
  sep_apply (InequList_seg_append_list l21); try easy.
  subst.
  entailer!.
Qed.

Lemma proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Proof.
  pre_process.
  Right.
  Exists l3_2 l4_2.
  rewrite PreH1.
  sep_apply inequlist_0_implies_nil.
  entailer!.
  + sep_apply InequList_seg_degeneration.
    subst.
    rewrite app_nil_r.
    entailer!.
  + subst.
    rewrite app_nil_r.
    auto.
Qed.

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_3_pure : generate_new_constraint_list_partial_solve_wit_3_pure.
Proof.
  pre_process.
  unfold InequList_nth_pos in PreH22.
  unfold InequList_nth_neg in PreH23.
  subst.
  specialize (PreH23 x ltac:(apply in_elt)).
  specialize (PreH22 x1 ltac:(apply in_elt)).
  entailer!.
Qed.

Lemma proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Proof. 
  pre_process.
  Exists l1.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - apply InequList_Zeros_range_empty.
  - apply self_LP_implies.
Qed.

Lemma proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Proof. 
  pre_process.
  Exists l3.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - pose proof (eliminate_keep_Zeros _ _ _ _ _ PreH9 PreH22 (ltac:(lia)) (ltac:(lia)) _ _ _ PreH10) as Keep.
    pose proof (eliminate_add_Zeros _ _ _ _ _ PreH9 PreH22 PreH23 (ltac:(lia)) (ltac:(lia)) _ _ _ PreH10) as Add.
    pose proof (generate_new_contraints_keep_Zeros _ _ _ _ _ _ PreH2 (proj1 Keep) (proj1 (proj2 Keep)) (ltac:(lia)) (ltac:(lia))).
    pose proof (generate_new_contraints_add_Zeros _ _ _ _ (cnt + 1) (n_pre + 1) PreH2 (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
    replace (cnt - 1 + 1) with cnt in * by lia.
    apply InequList_Zeros_range_extend_left ; try auto.
    + subst l3. apply InequList_Zeros_app ; try tauto.
    + subst l3. apply InequList_nth_zero_app ; try tauto. 
  - apply LP_implies_trans with (lp2:=l2_2); try tauto.
    apply FME_step_sound with cnt.
    rewrite PreH3.
    unfold form_BP in PreH10.
    destruct PreH10 as [BP1 [BP2 BP3]].
    rewrite BP3.
    rewrite BP1, BP2 in PreH2.
    constructor; tauto.
Qed. 

Lemma proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Proof. 
  pre_process.
  Exists l3.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - pose proof (eliminate_keep_Zeros _ _ _ _ _ PreH7 PreH20 (ltac:(lia)) (ltac:(lia)) _ _ _ PreH8) as Keep.
    pose proof (eliminate_add_Zeros _ _ _ _ _ PreH7 PreH20 PreH21 (ltac:(lia)) (ltac:(lia)) _ _ _ PreH8) as Add.
    pose proof (generate_new_contraints_keep_Zeros _ _ _ _ _ _ PreH2 (proj1 Keep) (proj1 (proj2 Keep)) (ltac:(lia)) (ltac:(lia))).
    pose proof (generate_new_contraints_add_Zeros _ _ _ _ (cnt + 1) (n_pre + 1) PreH2 (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
    replace (cnt - 1 + 1) with cnt in * by lia.
    apply InequList_Zeros_range_extend_left ; try auto.
    + subst l3. apply InequList_Zeros_app ; try tauto.
    + subst l3. apply InequList_nth_zero_app ; try tauto.
  - apply LP_implies_trans with (lp2:=l2_2); try tauto.
    apply FME_step_sound with cnt.
    rewrite PreH3.
    unfold form_BP in PreH8.
    destruct PreH8 as [BP1 [BP2 BP3]].
    rewrite BP3.
    rewrite BP1, BP2 in PreH2.
    constructor; tauto.
Qed.

Lemma proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Proof.
  pre_process.
  Exists r l2_2.
  entailer!.
  replace (cnt + 1) with 1 in * by lia.
  auto.
Qed.

Lemma proof_of_real_shadow_return_wit_3 : real_shadow_return_wit_3.
Proof.
  pre_process.
  rewrite PreH1.
  sep_apply inequlist_0_implies_nil.
  entailer!.
  do 3 sep_apply (store_ptr_undef_store_ptr).
  entailer!.
Qed.

Lemma proof_of_real_shadow_return_wit_5 : real_shadow_return_wit_5.
Proof.
  pre_process.
  rewrite PreH1.
  sep_apply inequlist_0_implies_nil.
  entailer!.
  do 3 sep_apply (store_ptr_undef_store_ptr).
  entailer!.
Qed.

Lemma proof_of_real_shadow_return_wit_7 : real_shadow_return_wit_7.
Proof. 
  pre_process.
  rewrite PreH1, PreH2.
  repeat sep_apply inequlist_0_implies_nil.
  Exists 0 nil.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    simpl.
    entailer!.
  - apply InequList_Zeros_nil.
  - apply LP_implies_nil.
Qed.

Lemma proof_of_real_shadow_return_wit_6 : real_shadow_return_wit_6.
Proof. 
  pre_process. subst.
  Exists 0 nil.
  entailer!.
  - do 3 sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply inequlist_0_implies_nil.
    simpl. entailer!.
  - apply InequList_Zeros_nil.
  - apply LP_implies_nil.
Qed.


Lemma proof_of_lia_deduction_entail_wit_1 : lia_deduction_entail_wit_1.
Proof.
  pre_process.
  Exists nil l2.
  rewrite app_nil_l.
  simpl. 
  entailer!.
  hnf. intros.
  inversion H.
Qed.
  
Lemma proof_of_lia_deduction_entail_wit_2 : lia_deduction_entail_wit_2.
Proof.
  pre_process.
  Exists (l21_2 ++ (x :: nil)) l0.
  entailer!.
  - sep_apply InequList_seg_append ; try (unfold NULL; lia).
    entailer!.
  - hnf. intros c Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply PreH6 ; auto.
    + destruct Hin as [Heq | Hin]; try lia.
      subst. lia.
      inversion Hin.
  - rewrite <- app_assoc. simpl.
    subst. auto.
Qed.

Lemma proof_of_lia_deduction_return_wit_2 : lia_deduction_return_wit_2.
Proof.
  pre_process.
  Exists BP0_4 p2_3.
  entailer!.
  eapply LP_Implies_UNSAT ; eauto.
  unfold UNSAT, satisfy_LP, satisfy_constraint, assignment.
  intros s Sat.
  assert (Hin : In x l2_2).
  {
    subst l2_2.
    apply in_app_iff.
    right. subst l22.
    left. auto.
  }
  specialize (Sat _ Hin).
  rewrite sum_prod_zeros in Sat.
  - unfold coef_Znth, Constraint_list in PreH2.
    rewrite Znth0_cons in PreH2.
    lia.
  - intros i Hi.
    apply (PreH13 x Hin i).
    lia.
Qed.
  
Lemma proof_of_lia_deduction_return_wit_1 : lia_deduction_return_wit_1.
Proof.
  pre_process.
  Exists BP0_4 p2_3 l2_2.
  entailer!.
  sep_apply InequList_seg_append_list; try (unfold NULL; lia).
  subst l2_2 l22.
  entailer!.
Qed.

Lemma proof_of_lia_deduction_which_implies_wit_1 : lia_deduction_which_implies_wit_1.
Proof.
  pre_process.
  prop_apply InequList_length.
  entailer!.
  sep_apply InequList_seg_app. 
  entailer!.
Qed.
