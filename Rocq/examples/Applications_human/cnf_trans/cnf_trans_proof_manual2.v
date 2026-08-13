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

Lemma proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures; dump_pre_spatial.
  destruct prop; simpl in * ; try lia.
Qed.

(* Already exported by cnf_trans_proof_auto.v.
Lemma proof_of_prop2cnf_entail_wit_1 : prop2cnf_entail_wit_1.
Proof.
  aggressive_pre_process.
Qed.
*)

Lemma proof_of_prop2cnf_entail_wit_2 : prop2cnf_entail_wit_2.
Proof.
  aggressive_pre_process.
  Exists op; Exists clist'; Exists pcnt'; Exists ccnt'.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed.

Lemma proof_of_prop2cnf_entail_wit_3 : prop2cnf_entail_wit_3.
Proof.
  aggressive_pre_process.
  Exists op.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
    all: rewrite <- PreH12; rewrite <- PreH14; lia.
Qed.

Lemma proof_of_prop2cnf_return_wit_3 : prop2cnf_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH5 as Hs1.
  pose proof PreH6 as Hs2.
  pose proof PreH7 as Hs3.
  Exists clist pcnt ccnt var.
  unfold store_predata.
  Intros y.
  Exists y.
  rewrite PreH1 in *.
  split_pure_spatial.
  { unfold SmtPTID, store_SmtProp.
    unfold SmtPTID.
    split_pure_spatial.
    { cancel.
      cancel.
      cancel.
      cancel. }
    { repeat split_pures; dump_pre_spatial.
      - unfold NULL in *; exact PreH3.
      - exact PreH2. } }
  { repeat split_pures; dump_pre_spatial.
    all:
      try (unfold make_predata, make_prop2cnf_ret, prop2cnf_logic; reflexivity);
      try (rewrite prop_cnt_inf_var in *; lia);
      try (pose proof SmtProp_size_nonneg (SmtV var); lia);
      try (unfold NULL in *; assumption);
      try assumption; try reflexivity; try lia. }
Qed.

Opaque Z.add Z.sub Z.mul Z.opp Z.of_nat Z.of_N Z.succ.

Lemma proof_of_prop2cnf_return_wit_2 : prop2cnf_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH20 in *.
  unfold SmtPTID in *.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_unary.
  repeat rewrite <- app_comm_cons.
  unfold app.
  remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
  remember (- p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
  assert (Hlogic:
    make_prop2cnf_ret
      (make_predata (c1 :: c2 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 2))
      (pcnt'_2 + 1) =
    prop2cnf_logic (SmtU op' sub_prop') (make_predata clist pcnt ccnt)).
  {
    unfold make_prop2cnf_ret, make_predata.
    simpl.
    remember (prop2cnf_logic sub_prop' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1''].
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    unfold make_prop2cnf_ret, make_predata in PreH13.
    rewrite <- PreH13 in Hstep1.
    inversion Hstep1.
    subst.
    reflexivity.
  }
  assert (Hlen:
    Zlength (c1 :: c2 :: clist'_2) <=
      Zlength clist + 4 * SmtProp_size (SmtU op' sub_prop')).
  {
    simpl SmtProp_size.
    repeat rewrite Zlength_cons.
    pose proof SmtProp_size_nonneg sub_prop'.
    lia.
  }
  assert (Hcnt: prop_cnt_inf (c1 :: c2 :: clist'_2) <= pcnt'_2 + 1).
  {
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in PreH11.
    pose proof Z.max_lub_l _ _ _ PreH11.
    pose proof Z.max_lub_r _ _ _ PreH11.
    apply Z.max_lub; rewrite H_c1, H_c2.
    + simpl.
      assert (p1 <= pcnt'_2 + 1) by lia.
      assert (- p1 <= pcnt'_2 + 1) by lia.
      assert (0 <= pcnt'_2 + 1) by lia.
      assert (max_cnf clist'_2 <= pcnt'_2 + 1) by lia.
      repeat apply Z.max_lub; try lia.
    + simpl.
      apply Z.abs_le.
      split.
      - repeat apply Z.min_glb; try lia.
      - pose proof Z.le_min_l (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
          (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
            (min_cnf clist'_2)).
        pose proof Z.le_min_l p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
          (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
            (min_cnf clist'_2))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  }
  Exists (c1 :: c2 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 2) (pcnt'_2 + 1) y0.
  split_pure_spatial.
  { simpl store_SmtProp.
    subst.
    Exists v.
    split_pure_spatial.
    { cancel (&( p_pre # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op") # Int |-> SmtPUID op').
      cancel (&( p_pre # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1") # Ptr |-> v).
      cancel (store_SmtProp v sub_prop').
      cancel (sll_cnf_list y0
        ((p1 :: pcnt'_2 + 1 :: 0 :: nil)
         :: (- p1 :: - (pcnt'_2 + 1) :: 0 :: nil) :: clist'_2)).
      cancel (&( p_pre # "SmtProp" ->ₛ "type") # Int |-> 6).
      cancel (&( data_pre # "PreData" ->ₛ "cnf_res") # Ptr |-> y0).
      cancel (&( data_pre # "PreData" ->ₛ "prop_cnt") # Int |-> (pcnt'_2 + 1)).
      cancel (&( data_pre # "PreData" ->ₛ "clause_cnt") # Int |-> (Zlength clist'_2 + 2)). }
    { dump_pre_spatial; unfold NULL in *; exact PreH21. } }
  { repeat split_pures; dump_pre_spatial.
    all:
      try (exact Hlogic);
      try reflexivity; try assumption;
      try (unfold NULL in *; assumption);
      try (simpl SmtProp_size; lia);
      try lia. }
Qed.

Lemma proof_of_prop2cnf_return_wit_1 : prop2cnf_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH1 as Hs.
  pose proof PreH2 as Hs0.
  pose proof PreH3 as Hs1.
  pose proof PreH4 as Hs2.
  pose proof PreH7 as Hs3.
  pose proof PreH8 as Hs4.
  pose proof PreH17 as Hs5.
  pose proof PreH18 as Hs6.
  pose proof PreH25 as Hs7.
  pose proof PreH26 as Hs8.
  pose proof PreH33 as Hs9.
  pose proof PreH34 as Hs10.
  pose proof PreH35 as Hs11.
  pose proof PreH27 as Hs12.
  pose proof PreH28 as Hs13.
  pose proof PreH5 as H.
  pose proof PreH6 as H0.
  pose proof PreH9 as H1.
  pose proof PreH10 as H2.
  pose proof PreH11 as H3.
  pose proof PreH12 as H4.
  pose proof PreH13 as H5.
  pose proof PreH14 as H6.
  pose proof PreH15 as H7.
  pose proof PreH16 as H8.
  pose proof PreH19 as H11.
  pose proof PreH20 as H10.
  pose proof PreH21 as H9.
  pose proof PreH22 as H12.
  pose proof PreH23 as H13.
  pose proof PreH24 as H14.
  pose proof PreH29 as H15.
  pose proof PreH30 as H16.
  pose proof PreH31 as H17.
  pose proof PreH32 as H18.
  pose proof PreH36 as H19.
  pose proof PreH37 as H20.
  pose proof PreH38 as H21.
  pose proof PreH39 as H22.
  rewrite H15 in *.
  unfold SmtPTID in *.
  clear H19.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  destruct op'; destruct (p1 ==? p2);
  repeat rewrite <- app_comm_cons;
  unfold app.
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        split_pure_spatial.
        { cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity. }
        { repeat split_pures; dump_pre_spatial; assumption. } }
      { Intros x x0 x1.
        split_pures; dump_pre_spatial.
        - exact H15.
        - unfold NULL in *; exact H16. }
    - repeat split_pures; dump_pre_spatial.
      all:
        try (unfold make_prop2cnf_ret, make_predata;
          simpl;
          remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1;
          destruct step1 as [data1 p1'];
          remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2;
          destruct step2 as [tmp clause_cnt];
          destruct tmp as [cnf_res prop_cnt];
          destruct cnf_res as [cnf_res0 prop_cnt0];
          unfold make_prop2cnf_ret, make_predata in H5, H9;
          rewrite <- H9 in Hstep1;
          inversion Hstep1;
          rewrite H26 in Hstep2;
          rewrite <- H5 in Hstep2;
          inversion Hstep2;
          destruct (p1 ==? p2); try contradiction;
          subst;
          reflexivity);
        try reflexivity;
        try (unfold NULL in *; assumption);
        try (repeat rewrite Zlength_cons; lia);
        try (simpl SmtProp_size in *; lia);
        try lia;
        try (rewrite H_c1, H_c2, H_c3; subst; simpl in H24; exact H24);
        try exact H24;
        try exact H23.
      rewrite H_c1, H_c2, H_c3; subst; simpl in H24;
        destruct (Z.eq_dec p2 p2) as [_ | Hneq]; [exact H24 | contradiction Hneq; reflexivity].
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        split_pure_spatial.
        * cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity.
        * repeat split_pures; dump_pre_spatial; assumption. }
      { Intros x x0 x1.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1 c2 c3.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_l
              (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
              (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
                (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
                  (min_cnf clist'_2))).
            pose proof Z.le_min_l p1
              (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)).
            remember
              (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
                (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
                  (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
                    (min_cnf clist'_2)))) as tmp1 eqn:H1000.
            remember (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
              as tmp2 eqn:H2000.
            clear H1000 H2000.
            lia. } }
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        split_pure_spatial.
        { cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity. }
        { repeat split_pures; dump_pre_spatial; assumption. } }
      { Intros x x0 x1.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1 c2 c3.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_l
              (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
                  (min_cnf clist'_2))).
            pose proof Z.le_min_l (- p1)
              (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
            remember
              (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                  (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
                    (min_cnf clist'_2)))) as tmp1 eqn:H1000.
            remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              as tmp2 eqn:H2000.
            clear H1000 H2000.
            lia. } }
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        split_pure_spatial.
        { cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity. }
        { repeat split_pures; dump_pre_spatial; assumption. } }
      { Intros x x0 x1.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1''].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1 c2 c3.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_l
              (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                  (min_cnf clist'_2))).
            pose proof Z.le_min_l (- p1)
              (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
            remember
              (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                  (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                    (min_cnf clist'_2)))) as tmp1 eqn:H1000.
            remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              as tmp2 eqn:H2000.
            clear H1000 H2000.
            lia. } }
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    - simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x.
        cancel.
        Exists x.
        cancel.
        cancel.
        sepcon_assoc_change.
        reflexivity. }
      { Intros x.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_r
              (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0)))
              (min_cnf clist'_2).
            remember
              (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0)))
                (min_cnf clist'_2)) as tmp1 eqn:H1000.
            clear H1000.
            lia. } }
  + remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        split_pure_spatial.
        { cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity. }
        { repeat split_pures; dump_pre_spatial; assumption. } }
      { Intros x x0 x1.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1 c2 c3.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_l
              (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                  (min_cnf clist'_2))).
            pose proof Z.le_min_l p1
              (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
            remember
              (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
                  (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                    (min_cnf clist'_2)))) as tmp1 eqn:H1000.
            remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
              as tmp2 eqn:H2000.
            clear H1000 H2000.
            lia. } }
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x.
        cancel.
        Exists x.
        cancel.
        cancel.
        sepcon_assoc_change.
        reflexivity. }
      { Intros x.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_r
              (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0)))
              (min_cnf clist'_2).
            remember
              (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0)))
                (min_cnf clist'_2)) as tmp1 eqn:H1000.
            clear H1000.
            lia. } }
  + remember (p1 :: p2 :: pcnt'_2 + 1 :: nil) as c1 eqn:H_c1.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c4 eqn:H_c4.
    Exists (c1 :: c2 :: c3 :: c4 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 4) (pcnt'_2 + 1) y0.
    split_pure_spatial.
    -
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      split_pure_spatial.
      { Intros x x0 x1 x2.
        cancel.
        Exists x.
        cancel.
        Exists x0.
        cancel.
        Exists x1.
        cancel.
        Exists x2.
        split_pure_spatial.
        { cancel.
          cancel.
          sepcon_assoc_change.
          reflexivity. }
        { repeat split_pures; dump_pre_spatial; assumption. } }
      { Intros x x0 x1 x2.
        repeat split_pures; dump_pre_spatial; try assumption; try lia. }
    - repeat split_pures; dump_pre_spatial.
      * unfold make_prop2cnf_ret, make_predata.
        simpl.
        remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
        destruct step1 as [data1 p1'].
        remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
        destruct step2 as [tmp clause_cnt].
        destruct tmp as [cnf_res prop_cnt].
        destruct cnf_res as [cnf_res0 prop_cnt0].
        unfold make_prop2cnf_ret, make_predata in H5, H9.
        rewrite <- H9 in Hstep1.
        inversion Hstep1.
        rewrite H26 in Hstep2.
        rewrite <- H5 in Hstep2.
        inversion Hstep2.
        destruct (p1 ==? p2); try contradiction.
        subst.
        reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * repeat rewrite Zlength_cons.
        lia.
      * simpl SmtProp_size in *.
        lia.
      * exact H19.
      * subst c1 c2 c3 c4.
        repeat rewrite Zlength_cons.
        lia.
      * unfold prop_cnt_inf.
        unfold prop_cnt_inf in H3.
        pose proof Z.max_lub_l _ _ _ H3.
        pose proof Z.max_lub_r _ _ _ H3.
        unfold make_prop2cnf_ret, make_predata in H5.
        pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
        apply Z.max_lub; rewrite H_c1, H_c2, H_c3, H_c4.
        { simpl.
          repeat apply Z.max_lub; try lia. }
        { simpl.
          apply Z.abs_le.
          split.
          { repeat apply Z.min_glb; try lia. }
          { pose proof Z.le_min_l
              (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
              (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
                (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
                  (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                    (min_cnf clist'_2)))).
            pose proof Z.le_min_l p1
              (Z.min p2 (Z.min (pcnt'_2 + 1) 0)).
            remember
              (Z.min (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
                (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
                  (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
                    (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0)))
                      (min_cnf clist'_2))))) as tmp1 eqn:H1000.
            remember (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
              as tmp2 eqn:H2000.
            clear H1000 H2000.
            lia. } }
Qed.

(* Already exported by cnf_trans_proof_auto.v.
Lemma proof_of_prop2cnf_partial_solve_wit_2_pure : prop2cnf_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

(* Already exported by cnf_trans_proof_auto.v.
Lemma proof_of_prop2cnf_partial_solve_wit_20_pure : prop2cnf_partial_solve_wit_20_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_prop2cnf_partial_solve_wit_19_pure_split_goal_1 :
  prop2cnf_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold make_predata, make_prop2cnf_ret in PreH21.
  assert (Hpcnt : pcnt'_1 <= pcnt'_2).
  { eapply pcnt_upper_incr; exact PreH21. }
  lia.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_19_pure_split_goal_2 :
  prop2cnf_partial_solve_wit_19_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold make_predata, make_prop2cnf_ret in PreH21.
  assert (Hpcnt : pcnt'_1 <= pcnt'_2).
  { eapply pcnt_upper_incr; exact PreH21. }
  lia.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_19_pure : prop2cnf_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_partial_solve_wit_19_pure_split_goal_1.
  Goal_apply proof_of_prop2cnf_partial_solve_wit_19_pure_split_goal_2.
Qed.

(* Already exported by cnf_trans_proof_auto.v.
Lemma proof_of_prop2cnf_partial_solve_wit_34_pure : prop2cnf_partial_solve_wit_34_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_prop2cnf_which_implies_wit_1 : prop2cnf_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_SmtProp_unfold.
  Exists (SmtPTID prop).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_2 : prop2cnf_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2.
  rewrite <- PreH1, PreH2.
  sep_apply store_SmtProp'_Binary.
  2: (rewrite <- PreH1; exact PreH2).
  Intros op lt rt y z.
  Exists z y op lt rt.
  split_pure_spatial.
  - cancel.
    sepcon_assoc_change.
    reflexivity.
  - repeat split_pures; dump_pre_spatial.
    + exact H0.
    + unfold NULL in *; exact H1.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_3_split_goal_1 :
  prop2cnf_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  apply prop_cnt_inf_Binary_r with (op := op) (lt := lt).
  exact PreH1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_3_split_goal_2 :
  prop2cnf_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  apply prop_cnt_inf_Binary_l with (op := op) (rt := rt).
  exact PreH1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_3 : prop2cnf_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_3_split_goal_1.
  Goal_apply proof_of_prop2cnf_which_implies_wit_3_split_goal_2.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_4_split_goal_1 :
  prop2cnf_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_4_split_goal_2 :
  prop2cnf_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_4 : prop2cnf_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_4_split_goal_1.
  Goal_apply proof_of_prop2cnf_which_implies_wit_4_split_goal_2.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_5_split_goal_1 :
  prop2cnf_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_5 : prop2cnf_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_5_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_6_split_goal_1 :
  prop2cnf_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in *.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_6 : prop2cnf_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_6_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_7_split_goal_1 :
  prop2cnf_which_implies_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH3 in *.
  simpl in PreH2.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_7 : prop2cnf_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_7_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_8_split_goal_1 :
  prop2cnf_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold make_predata, make_prop2cnf_ret in PreH1.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ PreH1.
  assert (prop_cnt_inf_SmtProp rt <= pcnt') by lia.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_8_split_goal_2 :
  prop2cnf_which_implies_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold make_predata, make_prop2cnf_ret in PreH1.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ PreH1.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_8 : prop2cnf_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_8_split_goal_1.
  Goal_apply proof_of_prop2cnf_which_implies_wit_8_split_goal_2.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_9_split_goal_1 :
  prop2cnf_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH3 in *.
  simpl in PreH2.
  pose proof SmtProp_size_nonneg lt.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_9 : prop2cnf_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_9_split_goal_1.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_10 : prop2cnf_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_predata.
  Intros y.
  Exists y.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption.
    pose proof prop_cnt_nneg clist'_2.
    lia.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_11_split_goal_1 :
  prop2cnf_which_implies_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH4 in *.
  simpl in PreH3.
  simpl.
  pose proof SmtProp_size_nonneg lt'.
  pose proof SmtProp_size_nonneg rt'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_11_split_goal_2 :
  prop2cnf_which_implies_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH4 in *.
  simpl in PreH3.
  simpl.
  pose proof SmtProp_size_nonneg lt'.
  pose proof SmtProp_size_nonneg rt'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_11 : prop2cnf_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_11_split_goal_1.
  Goal_apply proof_of_prop2cnf_which_implies_wit_11_split_goal_2.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_13 : prop2cnf_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_predata.
  Exists y''.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial.
    + unfold NULL in *; exact PreH1.
    + exact PreH2.
    + lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_15_split_goal_1 :
  prop2cnf_which_implies_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH3.
  simpl.
  assert (Zlength clist'_2 <= Zlength clist + 4 * (1 + SmtProp_size lt' + SmtProp_size rt') - 4) by lia.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_15 : prop2cnf_which_implies_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_15_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_17 : prop2cnf_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2.
  rewrite <- PreH1, PreH2.
  sep_apply store_SmtProp'_Unary.
  2: (rewrite <- PreH1; exact PreH2).
  Intros op prop0 y.
  Exists y op prop0.
  split_pure_spatial.
  - cancel.
    sepcon_assoc_change.
    reflexivity.
  - repeat split_pures; dump_pre_spatial.
    + exact H0.
    + unfold NULL in *; exact H1.
Qed. 


Lemma proof_of_prop2cnf_which_implies_wit_18_split_goal_1 :
  prop2cnf_which_implies_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  pose proof prop_cnt_inf_Unary_r _ _ _ PreH1.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_18 :
  prop2cnf_which_implies_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_18_split_goal_1.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_19_split_goal_1 :
  prop2cnf_which_implies_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_19 : prop2cnf_which_implies_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_19_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_20_split_goal_1 :
  prop2cnf_which_implies_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg sub_prop.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_20 : prop2cnf_which_implies_wit_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_20_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_21_split_goal_1 :
  prop2cnf_which_implies_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2 in *.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg sub_prop.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_21 : prop2cnf_which_implies_wit_21.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_21_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_22 : prop2cnf_which_implies_wit_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_predata.
  Intros y.
  Exists y.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption.
    pose proof prop_cnt_nneg clist'.
    lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_23_split_goal_1 :
  prop2cnf_which_implies_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH3 in *.
  simpl in PreH2.
  simpl.
  pose proof SmtProp_size_nonneg sub_prop'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_23_split_goal_2 :
  prop2cnf_which_implies_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH3 in *.
  simpl in PreH2.
  simpl.
  pose proof SmtProp_size_nonneg sub_prop'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_23 : prop2cnf_which_implies_wit_23.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_23_split_goal_1.
  Goal_apply proof_of_prop2cnf_which_implies_wit_23_split_goal_2.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_25 : prop2cnf_which_implies_wit_25.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_predata.
  Exists y''.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - repeat split_pures; dump_pre_spatial.
    + unfold NULL in *; exact PreH1.
    + exact PreH2.
    + lia.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_27_split_goal_1 :
  prop2cnf_which_implies_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2.
  simpl.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_27 : prop2cnf_which_implies_wit_27.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prop2cnf_which_implies_wit_27_split_goal_1.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_29 : prop2cnf_which_implies_wit_29.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  rewrite <- PreH2, PreH1.
  sep_apply store_SmtProp'_Var.
  2: (rewrite <- PreH2; exact PreH1).
  Intros var.
  Exists var.
  split_pure_spatial.
  - cancel; try (sepcon_assoc_change; reflexivity).
  - repeat split_pures; dump_pre_spatial.
    + exact H0.
    + exact H2.
    + unfold NULL in *; exact H1.
Qed.
