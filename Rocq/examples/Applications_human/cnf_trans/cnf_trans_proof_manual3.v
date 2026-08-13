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
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.cnf_trans Require Import smt_lang_lib.
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_lib.
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_clause_gen_binary_return_wit_5 : clause_gen_binary_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND) as Hbop. {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  pose proof PreH18 as Hs1.
  pose proof PreH19 as Hs2.
  pose proof PreH20 as Hs3.
  pose proof PreH21 as H24.
  pose proof PreH22 as H25.
  pose proof PreH23 as H26.
  pose proof PreH24 as Hprop_clist.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (- p1_pre :: - p2_pre :: p3_pre :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold as Hfold_store.
  sep_apply (Hfold_store retval_5 c1 retval); try easy.
  sep_apply (Hfold_store retval_6 c2 retval_2); try easy.
  sep_apply (Hfold_store retval_7 c3 retval_3); try easy.
  clear Hfold_store.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_len1.
  sep_apply (Hseg_len1 retval_5 c1 retval_6); try easy.
  sep_apply (Hseg_len1 retval_6 c2 retval_7); try easy.
  sep_apply (Hseg_len1 retval_7 c3 y); try easy.
  clear Hseg_len1.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_sll.
  unfold sll_cnf_list.
  sep_apply (Hseg_sll retval_7 y (c3 :: nil) clist); try easy.
  sep_apply (Hseg_sll retval_6 retval_7 (c2 :: nil) ((c3 :: nil) ++ clist)); try easy.
  sep_apply (Hseg_sll retval_5 retval_6 (c1 :: nil) ((c2 :: nil) ++ (c3 :: nil) ++ clist)); try easy.
  clear Hseg_sll.
  unfold store_predata.
  Exists retval_5.
  rewrite Hbop.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c1 :: c2 :: c3 :: clist) = ccnt + 3) as Hlen_app. {
    repeat rewrite Zlength_cons.
    rewrite PreH5.
    lia.
  }
  rewrite Hlen_app.
  assert (prop_cnt_inf (c1 :: c2 :: c3 :: clist) <= pcnt) as Hprop_app. {
    pose proof prop_cnt_nneg clist as Hcnt_nneg.
    clear - Hcnt_nneg Hs1 Hs2 Hs3 H24 H25 H26 Hprop_clist H_c1 H_c2 H_c3.
    assert (pcnt >= 1) as Hpcnt_ge1 by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) as Hclist_inf by lia.
    unfold prop_cnt_inf in Hclist_inf.
    pose proof Z.max_lub_l _ _ _ Hclist_inf.
    pose proof Z.max_lub_r _ _ _ Hclist_inf.
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      apply Z.abs_le.
      split.
      - repeat apply Z.min_glb; try lia.
      - pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - PreH4 PreH26 PreH27 Hprop_app Hs1 Hs2 Hs3.
  split_pure_spatial.
  - unfold sll_cnf_list.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try (unfold NULL; assumption); try reflexivity; try lia.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_6 : clause_gen_binary_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND) as Hbop. {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  pose proof PreH18 as Hs1.
  pose proof PreH19 as Hs2.
  pose proof PreH20 as Hs3.
  pose proof PreH21 as H24.
  pose proof PreH22 as H25.
  pose proof PreH23 as H26.
  pose proof PreH24 as Hprop_clist.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (- p1_pre :: p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold as Hfold_store.
  sep_apply (Hfold_store retval_5 c1 retval); try easy.
  sep_apply (Hfold_store retval_6 c2 retval_2); try easy.
  sep_apply (Hfold_store retval_7 c3 retval_3); try easy.
  clear Hfold_store.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_len1.
  sep_apply (Hseg_len1 retval_5 c1 retval_6); try easy.
  sep_apply (Hseg_len1 retval_6 c2 retval_7); try easy.
  sep_apply (Hseg_len1 retval_7 c3 y); try easy.
  clear Hseg_len1.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_sll.
  unfold sll_cnf_list.
  sep_apply (Hseg_sll retval_7 y (c3 :: nil) clist); try easy.
  sep_apply (Hseg_sll retval_6 retval_7 (c2 :: nil) ((c3 :: nil) ++ clist)); try easy.
  sep_apply (Hseg_sll retval_5 retval_6 (c1 :: nil) ((c2 :: nil) ++ (c3 :: nil) ++ clist)); try easy.
  clear Hseg_sll.
  unfold store_predata.
  Exists retval_5.
  rewrite Hbop.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c1 :: c2 :: c3 :: clist) = ccnt + 3) as Hlen_app. {
    repeat rewrite Zlength_cons.
    rewrite PreH5.
    lia.
  }
  rewrite Hlen_app.
  assert (prop_cnt_inf (c1 :: c2 :: c3 :: clist) <= pcnt) as Hprop_app. {
    pose proof prop_cnt_nneg clist as Hcnt_nneg.
    clear - Hcnt_nneg Hs1 Hs2 Hs3 H24 H25 H26 Hprop_clist H_c1 H_c2 H_c3.
    assert (pcnt >= 1) as Hpcnt_ge1 by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) as Hclist_inf by lia.
    unfold prop_cnt_inf in Hclist_inf.
    pose proof Z.max_lub_l _ _ _ Hclist_inf.
    pose proof Z.max_lub_r _ _ _ Hclist_inf.

    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.

      apply Z.abs_le.
      split.
      - 
        repeat apply Z.min_glb; try lia.
      - 
        pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - PreH4 PreH26 PreH27 Hprop_app Hs1 Hs2 Hs3.
  split_pure_spatial.
  - unfold sll_cnf_list.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try (unfold NULL; assumption); try reflexivity; try lia.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_7 : clause_gen_binary_return_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IMPLY) as Hbop.
  { destruct bop; unfold SmtPBID in *; try contradiction; try lia; reflexivity. }
  pose proof PreH18 as Hs1.
  pose proof PreH19 as Hs2.
  pose proof PreH20 as Hs3.
  pose proof PreH21 as Hs4.
  pose proof PreH22 as Hs5.
  pose proof PreH23 as Hs6.
  pose proof PreH24 as Hprop_clist.
  remember (p1_pre :: p3_pre :: 0 :: nil) as c1 eqn:H_c1.
  remember (- p2_pre :: p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (- p1_pre :: p2_pre :: - p3_pre :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold as Hfold_store.
  sep_apply (Hfold_store retval_5 c1 retval); try easy.
  sep_apply (Hfold_store retval_6 c2 retval_2); try easy.
  sep_apply (Hfold_store retval_7 c3 retval_3); try easy.
  clear Hfold_store.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_len1.
  sep_apply (Hseg_len1 retval_5 c1 retval_6); try easy.
  sep_apply (Hseg_len1 retval_6 c2 retval_7); try easy.
  sep_apply (Hseg_len1 retval_7 c3 y); try easy.
  clear Hseg_len1.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_sll.
  unfold sll_cnf_list.
  sep_apply (Hseg_sll retval_7 y (c3 :: nil) clist); try easy.
  sep_apply (Hseg_sll retval_6 retval_7 (c2 :: nil) ((c3 :: nil) ++ clist)); try easy.
  sep_apply (Hseg_sll retval_5 retval_6 (c1 :: nil) ((c2 :: nil) ++ (c3 :: nil) ++ clist)); try easy.
  clear Hseg_sll.
  unfold store_predata.
  Exists retval_5.
  rewrite Hbop.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c1 :: c2 :: c3 :: clist) = ccnt + 3) as Hlen_app.
  { repeat rewrite Zlength_cons. rewrite PreH5. lia. }
  rewrite Hlen_app.
  assert (prop_cnt_inf (c1 :: c2 :: c3 :: clist) <= pcnt) as Hprop_app.
  {
    pose proof prop_cnt_nneg clist as Hcnt_nneg.
    clear - Hcnt_nneg Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hprop_clist H_c1 H_c2 H_c3.
    assert (pcnt >= 1) as Hpcnt_ge1 by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) as Hclist_inf by lia.
    unfold prop_cnt_inf in Hclist_inf.
    pose proof Z.max_lub_l _ _ _ Hclist_inf.
    pose proof Z.max_lub_r _ _ _ Hclist_inf.
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    - simpl. repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      + repeat apply Z.min_glb; try lia.
      + pose proof Z.le_min_l (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
          (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
            (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
          (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
            (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - PreH4 PreH26 PreH27 Hprop_app Hs1 Hs2 Hs3.
  split_pure_spatial.
  - unfold sll_cnf_list.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try (unfold NULL; assumption); try reflexivity; try lia.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1 : clause_gen_binary_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  sep_apply (store_cnf_list_fold retval_5 (p3_pre :: 0 :: 0 :: nil) retval); auto.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_len1.
  sep_apply (Hseg_len1 retval_5 (p3_pre :: 0 :: 0 :: nil) y); auto.
  clear Hseg_len1.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_sll.
  unfold sll_cnf_list.
  sep_apply (Hseg_sll retval_5 y ((p3_pre :: 0 :: 0 :: nil) :: nil) clist); auto.
  clear Hseg_sll.
  unfold store_predata.
  Exists retval_5.
  assert (Hbop : bop = SMTPROP_IMPLY).
  { destruct bop; unfold SmtPBID in *; try contradiction; try lia; reflexivity. }
  rewrite Hbop in *.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  simpl.
  split_pure_spatial.
  - Intros tail.
    unfold sll_cnf_list.
    Exists tail.
    cancel.
    cancel.
    reflexivity.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    all: try solve [rewrite Zlength_cons; rewrite PreH3; lia].
    assert (Hclist_cnt : prop_cnt_inf clist <= pcnt) by lia.
    unfold prop_cnt_inf in Hclist_cnt.
    unfold prop_cnt_inf.
    simpl.
    pose proof Z.le_max_l (max_cnf clist) (Z.abs (min_cnf clist)) as Hmax_clist.
    pose proof Z.le_max_r (max_cnf clist) (Z.abs (min_cnf clist)) as Hmin_abs_clist.
    assert (Hmax_cnf_clist : max_cnf clist <= pcnt).
    { eapply Z.le_trans; [exact Hmax_clist | exact Hclist_cnt]. }
    assert (Habs_min_clist : Z.abs (min_cnf clist) <= pcnt).
    { eapply Z.le_trans; [exact Hmin_abs_clist | exact Hclist_cnt]. }
    assert (Hmin_clist_low : - pcnt <= min_cnf clist).
    { apply Z.abs_le in Habs_min_clist. lia. }
    assert (Hpcnt_nonneg : 0 <= pcnt) by lia.
    apply Z.max_lub.
    + apply Z.max_lub.
      * apply Z.max_lub.
        -- exact PreH18.
        -- apply Z.max_lub; exact Hpcnt_nonneg.
      * exact Hmax_cnf_clist.
    + apply Z.abs_le.
      split.
      * apply Z.min_glb.
        -- apply Z.min_glb.
           ++ lia.
           ++ apply Z.min_glb; lia.
        -- exact Hmin_clist_low.
      * eapply Z.le_trans.
        -- apply Z.le_min_l.
        -- eapply Z.le_trans.
           ++ apply Z.le_min_l.
           ++ exact PreH18.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_2 : clause_gen_binary_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  sep_apply (store_cnf_list_fold retval_5 (p3_pre :: 0 :: 0 :: nil) retval); auto.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_len1.
  sep_apply (Hseg_len1 retval_5 (p3_pre :: 0 :: 0 :: nil) y); auto.
  clear Hseg_len1.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next" as Hseg_sll.
  unfold sll_cnf_list.
  sep_apply (Hseg_sll retval_5 y ((p3_pre :: 0 :: 0 :: nil) :: nil) clist); auto.
  clear Hseg_sll.
  unfold store_predata.
  Exists retval_5.
  assert (Hbop : bop = SMTPROP_IFF).
  { destruct bop; unfold SmtPBID in *; simpl in *; try lia; reflexivity. }
  rewrite Hbop in *.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  simpl.
  split_pure_spatial.
  - Intros tail.
    unfold sll_cnf_list.
    Exists tail.
    cancel.
    cancel.
    reflexivity.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    all: try solve [rewrite Zlength_cons; rewrite PreH3; lia].
    assert (Hclist_cnt : prop_cnt_inf clist <= pcnt) by lia.
    unfold prop_cnt_inf in Hclist_cnt.
    unfold prop_cnt_inf.
    simpl.
    pose proof Z.le_max_l (max_cnf clist) (Z.abs (min_cnf clist)) as Hmax_clist.
    pose proof Z.le_max_r (max_cnf clist) (Z.abs (min_cnf clist)) as Hmin_abs_clist.
    assert (Hmax_cnf_clist : max_cnf clist <= pcnt).
    { eapply Z.le_trans; [exact Hmax_clist | exact Hclist_cnt]. }
    assert (Habs_min_clist : Z.abs (min_cnf clist) <= pcnt).
    { eapply Z.le_trans; [exact Hmin_abs_clist | exact Hclist_cnt]. }
    assert (Hmin_clist_low : - pcnt <= min_cnf clist).
    { apply Z.abs_le in Habs_min_clist. lia. }
    assert (Hpcnt_nonneg : 0 <= pcnt) by lia.
    apply Z.max_lub.
    + apply Z.max_lub.
      * apply Z.max_lub.
        -- exact PreH18.
        -- apply Z.max_lub; exact Hpcnt_nonneg.
      * exact Hmax_cnf_clist.
    + apply Z.abs_le.
      split.
      * apply Z.min_glb.
        -- apply Z.min_glb.
           ++ lia.
           ++ apply Z.min_glb; lia.
        -- exact Hmin_clist_low.
      * eapply Z.le_trans.
        -- apply Z.le_min_l.
        -- eapply Z.le_trans.
           ++ apply Z.le_min_l.
           ++ exact PreH18.
Qed.


Lemma proof_of_clause_gen_binary_which_implies_wit_1 : clause_gen_binary_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_predata.
  Intros y.
  Exists y.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed. 
