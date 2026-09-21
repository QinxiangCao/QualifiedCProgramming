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
From SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree Require Import binary_indexed_tree_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib.
Local Open Scope sac.

Lemma proof_of_lowbit_return_wit_1_split_goal_1 : lowbit_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_lowbit_return_wit_1 : lowbit_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_lowbit_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_add_safety_wit_1_split_goal_1 : add_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FenwickAddProgress_unfold in PreH10.
  destruct PreH10 as [Hcur_len [Hcur_zero [Hcursor_cover Hprogress]]].
  specialize (Hcursor_cover PreH1).
  specialize (Hprogress pos ltac:(lia)).
  destruct Hprogress as [Hupdated Hold].
  assert (Hcur : Znth pos bit_cur 0 = Znth pos bit_l 0).
  { apply Hold. right. lia. }
  unfold FenwickRep in PreH8.
  destruct PreH8 as [Ha_len [Hbit_len [Ha_zero Hnodes]]].
  specialize (Hnodes pos ltac:(lia)).
  pose proof (FenwickNodeSum_add_point__add_node_update
                a pos_pre delta_pre pos ltac:(lia) ltac:(lia)) as Hpoint.
  destruct Hpoint as [Hpoint_cover Hpoint_outside].
  specialize (Hpoint_cover Hcursor_cover).
  pose proof (FenwickNodeLo_bounds pos ltac:(lia)) as Hlo.
  specialize (PreH9 (FenwickNodeLo pos) pos ltac:(lia)).
  unfold FenwickNodeSum in Hnodes, Hpoint_cover.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_add_safety_wit_1_split_goal_2 : add_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FenwickAddProgress_unfold in PreH10.
  destruct PreH10 as [Hcur_len [Hcur_zero [Hcursor_cover Hprogress]]].
  specialize (Hcursor_cover PreH1).
  specialize (Hprogress pos ltac:(lia)).
  destruct Hprogress as [Hupdated Hold].
  assert (Hcur : Znth pos bit_cur 0 = Znth pos bit_l 0).
  { apply Hold. right. lia. }
  unfold FenwickRep in PreH8.
  destruct PreH8 as [Ha_len [Hbit_len [Ha_zero Hnodes]]].
  specialize (Hnodes pos ltac:(lia)).
  pose proof (FenwickNodeSum_add_point__add_node_update
                a pos_pre delta_pre pos ltac:(lia) ltac:(lia)) as Hpoint.
  destruct Hpoint as [Hpoint_cover Hpoint_outside].
  specialize (Hpoint_cover Hcursor_cover).
  pose proof (FenwickNodeLo_bounds pos ltac:(lia)) as Hlo.
  specialize (PreH9 (FenwickNodeLo pos) pos ltac:(lia)).
  unfold FenwickNodeSum in Hnodes, Hpoint_cover.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_add_safety_wit_1 : add_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_add_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_add_safety_wit_2_split_goal_1 : add_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_add_safety_wit_2_split_goal_2 : add_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_add_safety_wit_2 : add_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_add_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_add_entail_wit_1_split_goal_1 : add_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply FenwickAddProgress_unfold.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intros _.
        apply FenwickCovers_self.
        lia.
      * intros node Hnode.
        split.
        -- intros [Hcovers Hlt].
           unfold FenwickCovers in Hcovers.
           lia.
        -- intros _.
           reflexivity.
Qed.

Lemma proof_of_add_entail_wit_1_split_goal_2 : add_entail_wit_1_split_goal_2.
Proof.
  unfold add_entail_wit_1_split_goal_2. intros. eauto.
Qed.

Lemma proof_of_add_entail_wit_1 : add_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_add_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_add_entail_wit_2_split_goal_1 : add_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  match goal with
  | Hrep : FenwickRep a bit_l n_pre |- _ =>
      unfold FenwickRep in Hrep;
      destruct Hrep as [Halen [Hbitlen [Ha0 Hnodes]]]
  end.
  match goal with
  | Hprogress : FenwickAddProgress bit_l bit_cur_2 n_pre
        pos_pre pos delta_pre |- _ =>
      apply FenwickAddProgress_unfold in Hprogress;
      destruct Hprogress as [Hcurlen [Hcurzero [Hlive Hold]]]
  end.
  apply FenwickAddProgress_unfold.
  assert (Hposrange : 0 <= pos < Zlength bit_cur_2) by lia.
  split.
  - rewrite Zlength_replace_Znth.
    exact Hcurlen.
  - split.
    + rewrite Znth_replace_Znth_Diff.
      * exact Hcurzero.
      * exact Hposrange.
      * lia.
      * lia.
    + split.
      * intros Hsuccessor_live.
        apply Fenwick_add_successor_covers__add_progress_bitwise.
        -- lia.
        -- apply Hlive.
           lia.
      * intros node Hnode.
        assert (Hnoderange : 0 <= node < Zlength bit_cur_2) by lia.
        specialize (Hold node Hnode) as [Hold_updated Hold_unchanged].
        split.
        -- intros [Hnode_covers Hnode_before_successor].
           destruct (Z.lt_trichotomy node pos) as
               [Hnode_before | [Hnode_at | Hnode_after]].
           ++ rewrite Znth_replace_Znth_Diff.
              ** apply Hold_updated.
                 split; assumption.
              ** exact Hposrange.
              ** exact Hnoderange.
              ** lia.
           ++ subst node.
              rewrite Znth_replace_Znth_Same by exact Hposrange.
              rewrite Hold_unchanged.
              ** reflexivity.
              ** right; lia.
           ++ exfalso.
              assert (Hpos_covers : FenwickCovers pos pos_pre).
              { apply Hlive; lia. }
              pose proof
                (Fenwick_add_successor_gap__add_progress_bitwise
                   pos node ltac:(lia) ltac:(lia)) as Hgap.
              unfold FenwickCovers in Hpos_covers, Hnode_covers.
              lia.
        -- intros Hnode_unchanged.
           destruct (Z.eq_dec node pos) as [Hnode_at | Hnode_away].
           ++ subst node.
              assert (Hpos_covers : FenwickCovers pos pos_pre).
              { apply Hlive; lia. }
              destruct Hnode_unchanged as [Hnotcovers | Hsuccessor_before].
              ** contradiction.
              ** pose proof (FenwickLowbit_positive pos ltac:(lia)).
                 lia.
           ++ rewrite Znth_replace_Znth_Diff.
              ** apply Hold_unchanged.
                 destruct Hnode_unchanged as [Hnotcovers | Hsuccessor_before].
                 --- left; exact Hnotcovers.
                 --- right.
                     pose proof (FenwickLowbit_positive pos ltac:(lia)).
                     lia.
              ** exact Hposrange.
              ** exact Hnoderange.
              ** lia.
Qed.

Lemma proof_of_add_entail_wit_2_split_goal_2 : add_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  lia.
Qed.

Lemma proof_of_add_entail_wit_2_split_goal_3 : add_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  lia.
Qed.

Lemma proof_of_add_entail_wit_2 : add_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_add_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_add_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_add_return_wit_1_split_goal_1 : add_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FenwickRep in PreH8 |- *.
  unfold FenwickAddArray.
  apply FenwickAddProgress_unfold in PreH10.
  destruct PreH8 as [Ha_len [Hbit_len [Ha_zero Hnodes]]].
  destruct PreH10 as [Hcur_len [Hcur_zero [Hcursor_cover Hprogress]]].
  repeat split.
  - rewrite Zlength_replace_Znth, Ha_len.
    reflexivity.
  - lia.
  - rewrite (Znth_replace_Znth_Diff 0) by lia.
    exact Ha_zero.
  - intros node Hnode.
    specialize (Hnodes node Hnode).
    specialize (Hprogress node Hnode).
    destruct Hprogress as [Hupdated Hold].
    pose proof (FenwickNodeSum_add_point__add_node_update
                  a pos_pre delta_pre node ltac:(lia) ltac:(lia)) as Hpoint.
    destruct Hpoint as [Hpoint_cover Hpoint_outside].
    destruct (Z_le_gt_dec (FenwickNodeLo node) pos_pre) as [Hlo | Hlo];
      destruct (Z_le_gt_dec pos_pre node) as [Hhi | Hhi].
    + assert (Hcovers : FenwickCovers node pos_pre).
      { unfold FenwickCovers. lia. }
      rewrite Hupdated by (split; [exact Hcovers | lia]).
      rewrite Hnodes.
      symmetry.
      apply Hpoint_cover.
      exact Hcovers.
    + assert (Hnotcovers : ~ FenwickCovers node pos_pre).
      { unfold FenwickCovers. lia. }
      rewrite Hold by (left; exact Hnotcovers).
      rewrite Hnodes.
      symmetry.
      apply Hpoint_outside.
      exact Hnotcovers.
    + assert (Hnotcovers : ~ FenwickCovers node pos_pre).
      { unfold FenwickCovers. lia. }
      rewrite Hold by (left; exact Hnotcovers).
      rewrite Hnodes.
      symmetry.
      apply Hpoint_outside.
      exact Hnotcovers.
    + assert (Hnotcovers : ~ FenwickCovers node pos_pre).
      { unfold FenwickCovers. lia. }
      rewrite Hold by (left; exact Hnotcovers).
      rewrite Hnodes.
      symmetry.
      apply Hpoint_outside.
      exact Hnotcovers.
Qed.

Lemma proof_of_add_return_wit_1 : add_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_query_safety_wit_3_split_goal_1 : query_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (Fenwick_query_step_int_safe__query_step
       a bit_l n pos_pre pos sum
       PreH9 PreH10 ltac:(lia) ltac:(lia) ltac:(lia) PreH11)
    as Hsafe.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_3_split_goal_2 : query_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (Fenwick_query_step_int_safe__query_step
       a bit_l n pos_pre pos sum
       PreH9 PreH10 ltac:(lia) ltac:(lia) ltac:(lia) PreH11)
    as Hsafe.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_3 : query_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_query_safety_wit_4_split_goal_1 : query_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_4_split_goal_2 : query_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_query_safety_wit_4 : query_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_query_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_1 : query_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(apply FenwickQueryState_initial || lia || nia || int_auto).
Qed.

Lemma proof_of_query_entail_wit_1_split_goal_2 : query_entail_wit_1_split_goal_2.
Proof.
  unfold query_entail_wit_1_split_goal_2. intros. eauto.
Qed.

Lemma proof_of_query_entail_wit_1 : query_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_1 : query_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  eapply FenwickQueryState_step.
  - exact PreH10.
  - lia.
  - exact PreH12.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_2 : query_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  pose proof
    (Fenwick_query_step_int_safe__query_step
       a bit_l n pos_pre pos sum
       PreH10 PreH11 ltac:(lia) ltac:(lia) ltac:(lia) PreH12)
    as Hsafe.
  lia.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_3 : query_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  pose proof
    (Fenwick_query_step_int_safe__query_step
       a bit_l n pos_pre pos sum
       PreH10 PreH11 ltac:(lia) ltac:(lia) ltac:(lia) PreH12)
    as Hsafe.
  lia.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_4 : query_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  lia.
Qed.

Lemma proof_of_query_entail_wit_2_split_goal_5 : query_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (FenwickLowbit_bounds pos ltac:(lia)).
  lia.
Qed.

Lemma proof_of_query_entail_wit_2 : query_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_query_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_query_return_wit_1_split_goal_1 : query_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (pos = 0) by lia.
  subst pos.
  unfold FenwickQueryState in *.
  rewrite FenwickPrefixSum_zero in *.
  lia.
Qed.

Lemma proof_of_query_return_wit_1 : query_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_query_return_wit_1_split_goal_1.
Qed.

