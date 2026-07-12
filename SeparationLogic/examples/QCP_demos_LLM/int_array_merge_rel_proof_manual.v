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
From SimpleC.EE.QCP_demos_LLM Require Import int_array_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_lib.
Local Open Scope monad.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  pre_process.
  Exists l0. Exists (@nil Z). Exists (@nil Z). Exists s1. Exists s2. Exists (@nil Z).
  repeat (split_pure_spatial || split_pures).
  + rewrite (IntArray.seg_empty arr_pre p_pre p_pre).
    rewrite (IntArray.seg_empty arr_pre (q_pre + 1) (q_pre + 1)).
    rewrite (IntArray.seg_empty ret_pre p_pre p_pre).
    repeat (split_pure_spatial || split_pures).
    - cancel. cancel.
    - dump_pre_spatial. lia.
    - dump_pre_spatial. lia.
    - dump_pre_spatial. lia.
  + dump_pre_spatial.
    eapply (safeExec_prorefine (merge_rel s1 s2)).
    - unfold merge_rel, merge_from_mid_rel.
      reflexivity.
    - exact PreH1.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
Qed.

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof.
  pre_process.
  replace (i - i) with 0 by lia.
  replace (j - j) with 0 by lia.
  replace (k - k) with 0 by lia.
  replace (j + 1 - j) with 1 by lia.
  replace (k + 1 - k) with 1 by lia.
  prop_apply (IntArray.seg_Zlength arr_pre i (q_pre + 1) l1_2). Intros.
  prop_apply (IntArray.seg_Zlength arr_pre j (r_pre + 1) l2_2). Intros.
  prop_apply (IntArray.seg_Zlength ret_pre k (r_pre + 1)
    (replace_Znth 0 (Znth 0 l2_2 0) l6_2)). Intros.
  sep_apply_l_atomic (IntArray.seg_split_to_seg arr_pre j (j + 1) (r_pre + 1) l2_2).
  - dump_pre_spatial. lia.
  - replace (j + 1 - j) with 1 by lia.
    sep_apply_l_atomic (IntArray.seg_merge_to_seg arr_pre (q_pre + 1) j (j + 1) l5_2 (sublist 0 1 l2_2)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (IntArray.seg_split_to_seg ret_pre k (k + 1) (r_pre + 1) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
      * dump_pre_spatial. lia.
      * replace (k + 1 - k) with 1 by lia.
        sep_apply_l_atomic (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1) l3_2 (sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2))).
        -- dump_pre_spatial. lia.
        -- Exists (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
          Exists (l5_2 ++ sublist 0 1 l2_2).
          Exists l4_2.
          Exists l1_2.
          Exists (sublist 1 (r_pre + 1 - j) l2_2).
          Exists (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
          apply split_pure_and_spatial_goals.
          { apply int_array_merge_step_spatial_right. }
          { repeat apply split_pure_and_spatial_goals;
            try solve [dump_pre_spatial; lia].
            abstract (dump_pre_spatial;
              match goal with
              | Hlen1: Zlength l1_2 = _,
                Hlen2: Zlength l2_2 = _,
                Hlen6: Zlength (replace_Znth 0 (Znth 0 l2_2 0) l6_2) = _ |- _ =>
                  destruct l1_2 as [| x l1']; [rewrite Zlength_nil in Hlen1; lia |];
                  destruct l2_2 as [| y l2']; [rewrite Zlength_nil in Hlen2; lia |];
                  rewrite Zlength_replace_Znth in Hlen6;
                  destruct l6_2 as [| z l6']; [rewrite Zlength_nil in Hlen6; lia |];
              replace (i - i) with 0 in PreH1 by lia;
              replace (j - j) with 0 in PreH1 by lia;
              rewrite !Znth0_cons in PreH1;
              simpl in PreH1;
              cbn [replace_Znth sublist skipn firstn] in *;
              replace (sublist 1 (r_pre + 1 - j) (y :: l2')) with l2' by
                (unfold sublist; simpl;
                 rewrite firstn_all2;
                 [reflexivity
                 | rewrite <- Hlen2; rewrite Zlength_correct; rewrite Nat2Z.id; lia]);
              replace (sublist 0 1 (replace_Znth 0 (Znth 0 (y :: l2') 0) (z :: l6')))
                with (y :: nil) by reflexivity;
              unfold merge_from_mid_rel in PreH4 at 1;
              prog_nf in PreH4;
              unfold_loop in PreH4;
              prog_nf in PreH4;
              unfold merge_body in PreH4 at 1;
              prog_nf in PreH4;
              safe_choice_r PreH4; try lia;
              unfold merge_from_mid_rel;
              exact PreH4
              end). }
Qed.

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof.
  pre_process.
  replace (i - i) with 0 by lia.
  replace (j - j) with 0 by lia.
  replace (k - k) with 0 by lia.
  replace (i + 1 - i) with 1 by lia.
  replace (k + 1 - k) with 1 by lia.
  prop_apply (IntArray.seg_Zlength arr_pre i (q_pre + 1) l1_2). Intros.
  prop_apply (IntArray.seg_Zlength arr_pre j (r_pre + 1) l2_2). Intros.
  prop_apply (IntArray.seg_Zlength ret_pre k (r_pre + 1)
    (replace_Znth 0 (Znth 0 l1_2 0) l6_2)). Intros.
  sep_apply_l_atomic (IntArray.seg_split_to_seg arr_pre i (i + 1) (q_pre + 1) l1_2).
  - dump_pre_spatial. lia.
  - replace (i + 1 - i) with 1 by lia.
    sep_apply_l_atomic (IntArray.seg_merge_to_seg arr_pre p_pre i (i + 1) l4_2 (sublist 0 1 l1_2)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (IntArray.seg_split_to_seg ret_pre k (k + 1) (r_pre + 1) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
      * dump_pre_spatial. lia.
      * replace (k + 1 - k) with 1 by lia.
        sep_apply_l_atomic (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1) l3_2 (sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2))).
        -- dump_pre_spatial. lia.
        -- Exists (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
          Exists l5_2.
          Exists (l4_2 ++ sublist 0 1 l1_2).
          Exists (sublist 1 (q_pre + 1 - i) l1_2).
          Exists l2_2.
          Exists (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
          apply split_pure_and_spatial_goals.
          { apply int_array_merge_step_spatial_left. }
          { repeat apply split_pure_and_spatial_goals;
            try solve [dump_pre_spatial; lia].
            abstract (dump_pre_spatial;
              match goal with
              | Hlen1: Zlength l1_2 = _,
                Hlen2: Zlength l2_2 = _,
                Hlen6: Zlength (replace_Znth 0 (Znth 0 l1_2 0) l6_2) = _ |- _ =>
                  destruct l1_2 as [| x l1']; [rewrite Zlength_nil in Hlen1; lia |];
                  destruct l2_2 as [| y l2']; [rewrite Zlength_nil in Hlen2; lia |];
                  rewrite Zlength_replace_Znth in Hlen6;
                  destruct l6_2 as [| z l6']; [rewrite Zlength_nil in Hlen6; lia |];
              replace (i - i) with 0 in PreH1 by lia;
              replace (j - j) with 0 in PreH1 by lia;
              rewrite !Znth0_cons in PreH1;
              simpl in PreH1;
              cbn [replace_Znth sublist skipn firstn] in *;
              replace (sublist 1 (q_pre + 1 - i) (x :: l1')) with l1' by
                (unfold sublist; simpl;
                 rewrite firstn_all2;
                 [reflexivity
                 | rewrite <- Hlen1; rewrite Zlength_correct; rewrite Nat2Z.id; lia]);
              replace (sublist 0 1 (replace_Znth 0 (Znth 0 (x :: l1') 0) (z :: l6')))
                with (x :: nil) by reflexivity;
              unfold merge_from_mid_rel in PreH4 at 1;
              prog_nf in PreH4;
              unfold_loop in PreH4;
              prog_nf in PreH4;
              unfold merge_body in PreH4 at 1;
              prog_nf in PreH4;
              safe_choice_l PreH4; try lia;
              unfold merge_from_mid_rel;
              exact PreH4
              end). }
Qed.

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Proof.
  pre_process.
  prop_apply (IntArray.seg_valid arr_pre i (q_pre + 1) l1_2). Intros.
  Left.
  Exists l6_2. Exists l5_2. Exists l4_2. Exists l1_2. Exists l2_2. Exists l3_2.
  repeat (split_pure_spatial || split_pures).
  + repeat cancel.
  + dump_pre_spatial.
    match goal with
    | Hsafe: safeExec ATrue (merge_from_mid_rel l1_2 l2_2 l3_2) X |- _ =>
        exact Hsafe
    end.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
Qed.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Proof.
  pre_process.
  prop_apply (IntArray.seg_valid arr_pre j (r_pre + 1) l2_2). Intros.
  Exists l6_2. Exists l5_2. Exists l4_2. Exists l1_2. Exists l2_2. Exists l3_2.
  repeat (split_pure_spatial || split_pures).
  + repeat cancel.
  + dump_pre_spatial.
    match goal with
    | Hsafe: safeExec ATrue (merge_from_mid_rel l1_2 l2_2 l3_2) X |- _ =>
        exact Hsafe
    end.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
Qed.

Lemma proof_of_merge_entail_wit_4 : merge_entail_wit_4.
Proof.
  pre_process.
  replace (i - i) with 0 by lia.
  replace (k - k) with 0 by lia.
  replace (i + 1 - i) with 1 by lia.
  replace (k + 1 - k) with 1 by lia.
  prop_apply (IntArray.seg_Zlength arr_pre i (q_pre + 1) l1_2). Intros.
  prop_apply (IntArray.seg_Zlength arr_pre j (r_pre + 1) l2_2). Intros.
  prop_apply (IntArray.seg_Zlength ret_pre k (r_pre + 1)
    (replace_Znth 0 (Znth 0 l1_2 0) l6_2)). Intros.
  sep_apply_l_atomic (IntArray.seg_split_to_seg arr_pre i (i + 1) (q_pre + 1) l1_2).
  - dump_pre_spatial. lia.
  - replace (i + 1 - i) with 1 by lia.
    sep_apply_l_atomic (IntArray.seg_merge_to_seg arr_pre p_pre i (i + 1) l4_2 (sublist 0 1 l1_2)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (IntArray.seg_split_to_seg ret_pre k (k + 1) (r_pre + 1) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
      * dump_pre_spatial. lia.
      * replace (k + 1 - k) with 1 by lia.
        sep_apply_l_atomic (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1) l3_2 (sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2))).
        -- dump_pre_spatial. lia.
        -- Right.
          Exists (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
          Exists l5_2.
          Exists (l4_2 ++ sublist 0 1 l1_2).
          Exists (sublist 1 (q_pre + 1 - i) l1_2).
          Exists l2_2.
          Exists (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l1_2 0) l6_2)).
          apply split_pure_and_spatial_goals.
          { apply int_array_merge_step_spatial_left. }
          { repeat apply split_pure_and_spatial_goals;
            try solve [dump_pre_spatial; lia].
            abstract (dump_pre_spatial;
              match goal with
              | Hlen1: Zlength l1_2 = _,
                Hlen2: Zlength l2_2 = _,
                Hlen6: Zlength (replace_Znth 0 (Znth 0 l1_2 0) l6_2) = _ |- _ =>
              destruct l1_2 as [| x l1']; [rewrite Zlength_nil in Hlen1; lia |];
              destruct l2_2 as [| y l2'];
                [| rewrite Zlength_cons in Hlen2; pose proof (Zlength_nonneg l2'); lia];
              rewrite Zlength_replace_Znth in Hlen6;
              destruct l6_2 as [| z l6']; [rewrite Zlength_nil in Hlen6; lia |];
              replace (sublist 1 (q_pre + 1 - i) (x :: l1')) with l1' by
                (unfold sublist; simpl;
                 rewrite firstn_all2;
                 [reflexivity
                 | rewrite <- Hlen1; rewrite Zlength_correct; rewrite Nat2Z.id; lia]);
              replace (sublist 0 1 (replace_Znth 0 (Znth 0 (x :: l1') 0) (z :: l6')))
                with (x :: nil) by reflexivity;
              unfold merge_from_mid_rel in PreH2 at 1;
              prog_nf in PreH2;
              unfold_loop in PreH2;
              prog_nf in PreH2;
              unfold merge_body in PreH2 at 1;
              prog_nf in PreH2;
              unfold merge_from_mid_rel;
              prog_nf;
              unfold_loop;
              prog_nf;
              unfold merge_body at 1;
              destruct l1' as [| u l1''];
              prog_nf;
              try rewrite <- app_assoc;
              simpl;
              exact PreH2
              end). }
Qed.

Lemma proof_of_merge_entail_wit_5_2 : merge_entail_wit_5_2.
Proof.
  pre_process.
  prop_apply (IntArray.seg_length arr_pre i). Intros.
  destruct l1 as [| x l1']; [| simpl in H; lia].
  Exists l6_2. Exists l5_2. Exists l4_2. Exists l2_2. Exists l3_2.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_5_1 : merge_entail_wit_5_1.
Proof.
  pre_process.
  prop_apply (IntArray.seg_length arr_pre i). Intros.
  destruct l1 as [| x l1']; [| simpl in H; lia].
  Exists l6_2. Exists l5_2. Exists l4_2. Exists l2_2. Exists l3_2.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_6 : merge_entail_wit_6.
Proof.
  pre_process.
  replace (j - j) with 0 by lia.
  replace (k - k) with 0 by lia.
  replace (j + 1 - j) with 1 by lia.
  replace (k + 1 - k) with 1 by lia.
  prop_apply (IntArray.seg_Zlength arr_pre j (r_pre + 1) l2_2). Intros.
  prop_apply (IntArray.seg_Zlength ret_pre k (r_pre + 1)
    (replace_Znth 0 (Znth 0 l2_2 0) l6_2)). Intros.
  sep_apply_l_atomic (IntArray.seg_split_to_seg arr_pre j (j + 1) (r_pre + 1) l2_2).
  - dump_pre_spatial. lia.
  - replace (j + 1 - j) with 1 by lia.
    sep_apply_l_atomic (IntArray.seg_merge_to_seg arr_pre (q_pre + 1) j (j + 1) l5_2 (sublist 0 1 l2_2)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (IntArray.seg_split_to_seg ret_pre k (k + 1) (r_pre + 1) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
      * dump_pre_spatial. lia.
      * replace (k + 1 - k) with 1 by lia.
        sep_apply_l_atomic (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1) l3_2 (sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2))).
        -- dump_pre_spatial. lia.
        -- Exists (sublist 1 (r_pre + 1 - k) (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
          Exists (l5_2 ++ sublist 0 1 l2_2).
          Exists l4_2.
          Exists (sublist 1 (r_pre + 1 - j) l2_2).
          Exists (l3_2 ++ sublist 0 1 (replace_Znth 0 (Znth 0 l2_2 0) l6_2)).
          repeat (split_pure_spatial || split_pures).
          --- cancel. cancel. cancel.
          --- dump_pre_spatial.
            abstract (
              match goal with
              | Hlen2: Zlength l2_2 = _,
                Hlen6: Zlength (replace_Znth 0 (Znth 0 l2_2 0) l6_2) = _ |- _ =>
              destruct l2_2 as [| y l2']; [rewrite Zlength_nil in Hlen2; lia |];
              rewrite Zlength_replace_Znth in Hlen6;
              destruct l6_2 as [| z l6']; [rewrite Zlength_nil in Hlen6; lia |];
              replace (sublist 1 (r_pre + 1 - j) (y :: l2')) with l2' by
                (unfold sublist; simpl;
                 rewrite firstn_all2;
                 [reflexivity
                 | rewrite <- Hlen2; rewrite Zlength_correct; rewrite Nat2Z.id; lia]);
              replace (sublist 0 1 (replace_Znth 0 (Znth 0 (y :: l2') 0) (z :: l6')))
                with (y :: nil) by reflexivity;
              unfold merge_from_mid_rel in PreH2 at 1;
              prog_nf in PreH2;
              unfold_loop in PreH2;
              prog_nf in PreH2;
              unfold merge_body in PreH2 at 1;
              prog_nf in PreH2;
              unfold merge_from_mid_rel;
              prog_nf;
              unfold_loop;
              prog_nf;
              unfold merge_body at 1;
              destruct l2' as [| u l2''];
              prog_nf;
              try rewrite <- app_assoc;
              simpl;
              exact PreH2
              end).
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
          --- dump_pre_spatial. lia.
Qed.

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.seg_valid arr_pre j (r_pre + 1) l2). Intros.
  prop_apply (IntArray.seg_Zlength arr_pre j (r_pre + 1) l2). Intros.
  assert (j = r_pre + 1) by lia.
  subst j.
  subst i.
  assert (k = r_pre + 1) by lia.
  subst k.
  destruct l2 as [| x l2'];
    [| match goal with Hlen: Zlength (x :: l2') = _ |- _ =>
         rewrite Zlength_cons in Hlen; pose proof (Zlength_nonneg l2'); lia
       end].
  rewrite (IntArray.seg_empty arr_pre (r_pre + 1) (r_pre + 1)).
  Intros_p Hempty.
  replace (p_pre + (q_pre + 1 - p_pre) + (r_pre + 1 - (q_pre + 1)))
    with (r_pre + 1) by lia.
  prop_apply (IntArray.seg_Zlength ret_pre (r_pre + 1) (r_pre + 1) l6). Intros.
  destruct l6 as [| x l6'];
    [| match goal with Hlen: Zlength (x :: l6') = _ |- _ =>
         rewrite Zlength_cons in Hlen; pose proof (Zlength_nonneg l6'); lia
       end].
  rewrite (IntArray.seg_empty ret_pre (r_pre + 1) (r_pre + 1)).
  Intros_p Hempty_ret.
  Exists (l4 ++ l5). Exists l3.
  sep_apply_l_atomic (IntArray.seg_merge_to_seg arr_pre p_pre (q_pre + 1) (r_pre + 1) l4 l5).
  - dump_pre_spatial. lia.
  - repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial.
      unfold merge_from_mid_rel in PreH2.
      prog_nf in PreH2.
      unfold_loop in PreH2.
      prog_nf in PreH2.
      unfold merge_body in PreH2.
      prog_nf in PreH2.
      rewrite app_nil_r in PreH2.
      exact PreH2.
Qed.

Lemma proof_of_mergeSort_safety_wit_1 : mergeSort_safety_wit_1.
Proof.
  pre_process.
  repeat (split_pure_spatial || split_pures).
  + dump_pre_spatial.
    assert ((r_pre - l_pre) ÷ 2 < r_pre - l_pre).
    {
      apply Z.quot_lt_upper_bound ; try lia.
    }
    lia.
  + dump_pre_spatial.
    assert (0 <= (r_pre - l_pre) ÷ 2).
    {
      apply Z.quot_le_lower_bound ; try lia.
    }
    lia.
Qed.

Lemma proof_of_mergeSort_entail_wit_1 : mergeSort_entail_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.seg_Zlength arr_pre l_pre (r_pre + 1) s1_low_level_spec).
  Intros.
  Exists (sublist 0 (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) s1_low_level_spec).
  Exists (sublist (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) (r_pre + 1 - l_pre) s1_low_level_spec).
  repeat (split_pure_spatial || split_pures).
  + sep_apply_l_atomic (IntArray.seg_split_to_seg arr_pre l_pre (l_pre + (r_pre - l_pre) ÷ 2 + 1) (r_pre + 1) s1_low_level_spec).
    - dump_pre_spatial.
      assert (0 <= (r_pre - l_pre) ÷ 2).
      { apply Z.quot_le_lower_bound; try lia. }
      assert ((r_pre - l_pre) ÷ 2 < r_pre - l_pre).
      { apply Z.quot_lt_upper_bound; try lia. }
      lia.
    - sep_apply_l_atomic (IntArray.seg_split_to_seg ret_pre l_pre (l_pre + (r_pre - l_pre) ÷ 2 + 1) (r_pre + 1) s1_low_level_spec).
      * dump_pre_spatial.
        assert (0 <= (r_pre - l_pre) ÷ 2).
        { apply Z.quot_le_lower_bound; try lia. }
        assert ((r_pre - l_pre) ÷ 2 < r_pre - l_pre).
        { apply Z.quot_lt_upper_bound; try lia. }
        lia.
      * cancel.
  + dump_pre_spatial.
    rewrite (gmergesortrec_unfold s1_low_level_spec) in PreH2.
    unfold gmergesortrec_f in PreH2.
    apply safeExec_choice_r in PreH2.
    safe_step PreH2.
    * prove_by_one_abs_step ((sublist 0 (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) s1_low_level_spec),
        (sublist (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) (r_pre + 1 - l_pre) s1_low_level_spec)).
      unfold ext_split.
      apply hseval_stateless_ret.
      rewrite <- (sublist_self s1_low_level_spec (Zlength s1_low_level_spec)) at 1 by reflexivity.
      rewrite (sublist_split 0 (Zlength s1_low_level_spec)
        (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) s1_low_level_spec).
      2: {
        assert (0 <= (r_pre - l_pre) ÷ 2).
        { apply Z.quot_le_lower_bound; try lia. }
        lia.
      }
      2: {
        assert ((r_pre - l_pre) ÷ 2 < r_pre - l_pre).
        { apply Z.quot_lt_upper_bound; try lia. }
        match goal with
        | Hlen: Zlength s1_low_level_spec = _ |- _ => rewrite Hlen
        end.
        lia.
      }
      match goal with
      | Hlen: Zlength s1_low_level_spec = _ |- _ => rewrite Hlen
      end.
      apply Permutation_refl.
    * match goal with
      | Hlen: Zlength s1_low_level_spec = _ |- _ => rewrite Hlen
      end.
      lia.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
  + dump_pre_spatial. exact PreH5.
  + dump_pre_spatial. exact PreH1.
  + dump_pre_spatial.
    assert (0 <= (r_pre - l_pre) ÷ 2).
    { apply Z.quot_le_lower_bound; try lia. }
    lia.
  + dump_pre_spatial.
    assert ((r_pre - l_pre) ÷ 2 < r_pre - l_pre).
    { apply Z.quot_lt_upper_bound; try lia. }
    lia.
Qed.

Lemma proof_of_mergeSort_entail_wit_2 : mergeSort_entail_wit_2.
Proof.
  pre_process.
  Exists l2_3. Exists l2_2. Exists l1_2.
  repeat (split_pure_spatial || split_pures).
  + cancel. cancel.
  + dump_pre_spatial.
    unfold applyf in PreH1.
    unfold gmergesortrec_loc1 in PreH1.
    unfold mergesortrec_loc2.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
  + dump_pre_spatial. exact PreH5.
  + dump_pre_spatial. exact PreH6.
  + dump_pre_spatial. exact PreH7.
Qed.

Lemma proof_of_mergeSort_entail_wit_3 : mergeSort_entail_wit_3.
Proof.
  pre_process.
  Exists (l3 ++ l2). Exists l1. Exists l1_2.
  repeat (split_pure_spatial || split_pures).
  + sep_apply_l_atomic (IntArray.seg_merge_to_seg ret_pre l_pre (m + 1) (r_pre + 1) l3 l2).
    - dump_pre_spatial. lia.
    - cancel.
  + dump_pre_spatial.
    unfold applyf in PreH1.
    unfold mergesortrec_loc2 in PreH1.
    exact PreH1.
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
  + dump_pre_spatial. exact PreH5.
  + dump_pre_spatial. exact PreH6.
  + dump_pre_spatial. exact PreH7.
Qed.

Lemma proof_of_mergeSort_return_wit_2 : mergeSort_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.seg_length arr_pre l_pre). Intros.
  Exists s1_low_level_spec. Exists s1_low_level_spec.
  entailer!.
  destruct s1_low_level_spec as [| x xs]. simpl in H. lia.
  destruct xs as [| y ys]. 2: { simpl in H. lia. }
  rewrite (gmergesortrec_unfold _) in PreH2.
  unfold gmergesortrec_f in PreH2.
  safe_choice_l PreH2.
  eapply highstependret_derive with (P' := (fun _ => ATrue)); eauto.
  apply hseval_stateless_ret.
  unfold ext_sort.
  easy.
Qed.

Lemma proof_of_mergeSort_derive_low_level_spec_aux_by_low_level_spec : mergeSort_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l0_low_level_spec_aux. Exists X_low_level_spec.
  split_pure_spatial.
  - cancel (IntArray.seg arr_pre l_pre (r_pre + 1) l0_low_level_spec_aux).
    cancel (IntArray.seg ret_pre l_pre (r_pre + 1) l0_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros s3. Intros s2.
    Exists s3. Exists s2.
    split_pure_spatial.
    + cancel (IntArray.seg arr_pre l_pre (r_pre + 1) s3).
      cancel (IntArray.seg ret_pre l_pre (r_pre + 1) s2).
    + dump_pre_spatial.
      unfold applyf.
      apply (Hsafe_cont ATrue s2).
      exact H.
  - split_pures.
    + dump_pre_spatial. exact Hsafe_first.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
Qed.
