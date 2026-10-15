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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P048_1607E_robot_on_the_board_1_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P048_1607E_robot_on_the_board_1_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold WindowFits; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(apply prefix_window_zero__initialization).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(exact PreH9).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold IntArray.full, store_array.
  simpl store_array_rec.
  replace (1 - 0) with 1 by lia.
  replace (row_pre + 0) with row_pre by lia.
  replace (col_pre + 0) with col_pre by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as
      (_ & _ & Hc & _ & _ & Hall & _ & _ & _ & _).
  specialize (Hall i ltac:(lia)) as [_ Hcol].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by (pose proof (Zlength_nonneg moves); lia).
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as
      (_ & _ & Hc & _ & _ & Hall & _ & _ & _ & _).
  specialize (Hall i ltac:(lia)) as [_ Hcol].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by (pose proof (Zlength_nonneg moves); lia).
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength moves).
  {
    destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
    assert (i = Zlength moves) by lia.
    subst i.
    rewrite app_Znth2 in PreH30 by (pose proof (Zlength_nonneg moves); lia).
    replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
    rewrite Znth0_cons in PreH30.
    contradiction.
  }
  assert (Hcmd : Znth i moves 0 = 85).
  {
    rewrite app_Znth1 in PreH31 by lia.
    lia.
  }
  eapply prefix_window_step_up_new_min__up_new_min; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by (pose proof (Zlength_nonneg moves); lia).
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [Hi [Hr [Hc [Hrow0 [Hcol0 [Hbounds Hextrema]]]]]].
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as [Hrow Hcol].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_4_split_goal_2 : solver_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [Hi [Hr [Hc [Hrow0 [Hcol0 [Hbounds Hextrema]]]]]].
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as [Hrow Hcol].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_5_split_goal_2 : solver_entail_wit_2_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_6_split_goal_1 : solver_entail_wit_2_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [Hi [Hr [Hc [Hrow0 [Hcol0 [Hbounds Hextrema]]]]]].
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as [Hrow Hcol].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_6_split_goal_2 : solver_entail_wit_2_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_7_split_goal_1 : solver_entail_wit_2_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [Hi [_ [Hc [_ [_ [Hall _]]]]]].
  specialize (Hall i ltac:(lia)).
  rewrite <- Hc in Hall.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_7_split_goal_2 : solver_entail_wit_2_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  rewrite Z.sub_diag in PreH30.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_7_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_8_split_goal_1 : solver_entail_wit_2_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [Hi [_ [Hc [_ [_ [Hall _]]]]]].
  specialize (Hall i ltac:(lia)).
  rewrite <- Hc in Hall.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_8_split_goal_2 : solver_entail_wit_2_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  rewrite Z.sub_diag in PreH30.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_8_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_9_split_goal_1 : solver_entail_wit_2_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength moves).
  {
    destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
    assert (i = Zlength moves) by lia.
    subst i.
    rewrite app_Znth2 in PreH30 by lia.
    rewrite Z.sub_diag in PreH30.
    simpl in PreH30.
    contradiction.
  }
  assert (Hcmd : Znth i moves 0 = 85).
  {
    rewrite app_Znth1 in PreH31 by lia.
    lia.
  }
  eapply prefix_window_step_up_inside__up_inside; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_9_split_goal_2 : solver_entail_wit_2_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.lt_ge_cases i (Zlength moves)); [lia |].
  assert (i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  rewrite Z.sub_diag in PreH30.
  simpl in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_9 : solver_entail_wit_2_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_10_split_goal_1 : solver_entail_wit_2_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & Hc & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as (_ & Hcol).
  rewrite <- Hc in Hcol.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_10_split_goal_2 : solver_entail_wit_2_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi].
  - exact Hi.
  - rewrite app_Znth2 in PreH30 by lia.
  replace (i - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_10 : solver_entail_wit_2_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_10_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_11_split_goal_1 : solver_entail_wit_2_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & Hc & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as (_ & Hcol).
  rewrite <- Hc in Hcol.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_11_split_goal_2 : solver_entail_wit_2_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi].
  - exact Hi.
  - rewrite app_Znth2 in PreH30 by lia.
  replace (i - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_11 : solver_entail_wit_2_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_11_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_12_split_goal_1 : solver_entail_wit_2_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  destruct Hbounds as (Hrow & _).
  rewrite <- Hr in Hrow.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_12_split_goal_2 : solver_entail_wit_2_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi].
  - exact Hi.
  - rewrite app_Znth2 in PreH30 by lia.
  replace (i - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_12 : solver_entail_wit_2_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_12_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_13_split_goal_1 : solver_entail_wit_2_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as
    [_ [_ [Hc [_ [_ [Hall _]]]]]].
  pose proof (Hall i ltac:(lia)) as Hcurrent.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_13_split_goal_2 : solver_entail_wit_2_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__down_new_max in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_13 : solver_entail_wit_2_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_13_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_13_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_14_split_goal_1 : solver_entail_wit_2_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as
    [_ [_ [Hc [_ [_ [Hall _]]]]]].
  pose proof (Hall i ltac:(lia)) as Hcurrent.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_14_split_goal_2 : solver_entail_wit_2_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__down_new_max in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_14 : solver_entail_wit_2_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_14_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_14_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_15_split_goal_1 : solver_entail_wit_2_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : 0 <= i < Zlength moves).
  {
    destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
    - subst i.
      rewrite Znth_app_last__down_new_max in PreH30.
      contradiction.
    - lia.
  }
  assert (Hcmd : Znth i moves 0 = 68).
  {
    rewrite <- (Znth_app_left__down_new_max moves (0 :: nil) 0 i Hi).
    symmetry. exact PreH32.
  }
  eapply prefix_window_step_down_new_max__down_new_max; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_15_split_goal_2 : solver_entail_wit_2_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__down_new_max in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_15 : solver_entail_wit_2_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_15_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_15_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_16_split_goal_1 : solver_entail_wit_2_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [_ [_ [Hcol [_ [_ [Hall _]]]]]].
  specialize (Hall i ltac:(lia)) as [_ Hbounds].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_16_split_goal_2 : solver_entail_wit_2_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
  assert (Heq : i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_16 : solver_entail_wit_2_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_16_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_16_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_17_split_goal_1 : solver_entail_wit_2_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as [_ [_ [Hcol [_ [_ [Hall _]]]]]].
  specialize (Hall i ltac:(lia)) as [_ Hbounds].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_17_split_goal_2 : solver_entail_wit_2_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
  assert (Heq : i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_17 : solver_entail_wit_2_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_17_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_17_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_18_split_goal_1 : solver_entail_wit_2_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  assert (Hlt : i < Zlength moves).
  {
    destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge].
    - exact Hlt.
    - exfalso.
      assert (Heq : i = Zlength moves) by lia.
      subst i.
      rewrite app_Znth2 in PreH30 by lia.
      replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
      rewrite Znth0_cons in PreH30.
      contradiction.
  }
  assert (Hcmd : Znth i moves 0 = 68).
  {
    rewrite app_Znth1 in PreH32 by lia.
    lia.
  }
  eapply prefix_window_step_down_inside__down_inside.
  - lia.
  - exact Hcmd.
  - exact PreH28.
  - lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_18_split_goal_2 : solver_entail_wit_2_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
  assert (Heq : i = Zlength moves) by lia.
  subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_18 : solver_entail_wit_2_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_18_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_18_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_19_split_goal_1 : solver_entail_wit_2_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as [Hrow _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_19_split_goal_2 : solver_entail_wit_2_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__left_impossible_low_row in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_19 : solver_entail_wit_2_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_19_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_19_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_20_split_goal_1 : solver_entail_wit_2_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as [Hrow _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_20_split_goal_2 : solver_entail_wit_2_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__left_impossible_low_row in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_20 : solver_entail_wit_2_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_20_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_20_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_21_split_goal_1 : solver_entail_wit_2_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as [Hrow _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_21_split_goal_2 : solver_entail_wit_2_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i (Zlength moves)) as [Heq | Hneq].
  - subst i.
    rewrite Znth_app_last__left_impossible_low_row in PreH30.
    contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2_21 : solver_entail_wit_2_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_21_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_21_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_22_split_goal_1 : solver_entail_wit_2_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as (Hrow & _).
  unfold RowOffset in Hr, Hrow.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_22_split_goal_2 : solver_entail_wit_2_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)); [lia |].
  exfalso.
  apply PreH30.
  rewrite app_Znth2 by lia.
  replace (i - Zlength moves) with 0 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_22 : solver_entail_wit_2_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_22_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_22_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_23_split_goal_1 : solver_entail_wit_2_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as (Hrow & _).
  unfold RowOffset in Hr, Hrow.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_23_split_goal_2 : solver_entail_wit_2_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)); [lia |].
  exfalso.
  apply PreH30.
  rewrite app_Znth2 by lia.
  replace (i - Zlength moves) with 0 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_23 : solver_entail_wit_2_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_23_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_23_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_24_split_goal_1 : solver_entail_wit_2_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hall & _).
  specialize (Hall i ltac:(lia)).
  destruct Hall as (Hrow & _).
  unfold RowOffset in Hr, Hrow.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_24_split_goal_2 : solver_entail_wit_2_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)); [lia |].
  exfalso.
  apply PreH30.
  rewrite app_Znth2 by lia.
  replace (i - Zlength moves) with 0 by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_24 : solver_entail_wit_2_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_24_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_24_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_25_split_goal_1 : solver_entail_wit_2_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (nonzero_Znth_sentinel_lt__left_valid_row moves i
    (conj PreH12 PreH13) PreH30) as Hi.
  rewrite app_Znth1 in PreH33 by exact (conj PreH12 Hi).
  pose proof (prefix_window_step_left_cases__left_valid_row
    moves i r c minr maxr minc maxc (conj PreH12 Hi)
    (eq_sym PreH33) PreH28) as Hstep.
  rewrite Z.min_r in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_2_25_split_goal_2 : solver_entail_wit_2_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (nonzero_Znth_sentinel_lt__left_valid_row moves i
    (conj PreH12 PreH13) PreH30).
Qed.

Lemma proof_of_solver_entail_wit_2_25 : solver_entail_wit_2_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_25_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_25_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_26_split_goal_1 : solver_entail_wit_2_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & Hc & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  rewrite <- Hr, <- Hc in Hbounds.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_26_split_goal_2 : solver_entail_wit_2_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (nonzero_Znth_sentinel_lt__left_valid_row moves i
    (conj PreH12 PreH13) PreH30).
Qed.

Lemma proof_of_solver_entail_wit_2_26 : solver_entail_wit_2_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_26_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_26_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_27_split_goal_1 : solver_entail_wit_2_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (nonzero_Znth_sentinel_lt__left_valid_row moves i
    (conj PreH12 PreH13) PreH30) as Hi.
  rewrite app_Znth1 in PreH33 by exact (conj PreH12 Hi).
  pose proof (prefix_window_step_left_cases__left_valid_row
    moves i r c minr maxr minc maxc (conj PreH12 Hi)
    (eq_sym PreH33) PreH28) as Hstep.
  rewrite Z.min_l in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_2_27_split_goal_2 : solver_entail_wit_2_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (nonzero_Znth_sentinel_lt__left_valid_row moves i
    (conj PreH12 PreH13) PreH30).
Qed.

Lemma proof_of_solver_entail_wit_2_27 : solver_entail_wit_2_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_27_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_27_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_28_split_goal_1 : solver_entail_wit_2_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold PrefixWindow in PreH28;
    destruct PreH28 as
      [Hi [Hr [Hc [Hrow0 [Hcol0 [Hall [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]];
    destruct (Hall i ltac:(lia)) as [Hrow Hcol];
    lia).
Qed.

Lemma proof_of_solver_entail_wit_2_28_split_goal_2 : solver_entail_wit_2_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    destruct (Z.eq_dec i (Zlength moves));
    [ subst i;
      unfold Znth in PreH30;
      rewrite Zlength_correct, Nat2Z.id, nth_middle in PreH30;
      lia
    | lia ]).
Qed.

Lemma proof_of_solver_entail_wit_2_28 : solver_entail_wit_2_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_28_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_28_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_29_split_goal_1 : solver_entail_wit_2_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold PrefixWindow in PreH28;
    destruct PreH28 as
      [Hi [Hr [Hc [Hrow0 [Hcol0 [Hall [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]];
    destruct (Hall i ltac:(lia)) as [Hrow Hcol];
    lia).
Qed.

Lemma proof_of_solver_entail_wit_2_29_split_goal_2 : solver_entail_wit_2_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    destruct (Z.eq_dec i (Zlength moves));
    [ subst i;
      unfold Znth in PreH30;
      rewrite Zlength_correct, Nat2Z.id, nth_middle in PreH30;
      lia
    | lia ]).
Qed.

Lemma proof_of_solver_entail_wit_2_29 : solver_entail_wit_2_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_29_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_29_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_30_split_goal_1 : solver_entail_wit_2_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    unfold PrefixWindow in PreH28;
    destruct PreH28 as
      [Hi [Hr [Hc [Hrow0 [Hcol0 [Hall [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]];
    destruct (Hall i ltac:(lia)) as [Hrow Hcol];
    lia).
Qed.

Lemma proof_of_solver_entail_wit_2_30_split_goal_2 : solver_entail_wit_2_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(
    destruct (Z.eq_dec i (Zlength moves));
    [ subst i;
      unfold Znth in PreH30;
      rewrite Zlength_correct, Nat2Z.id, nth_middle in PreH30;
      lia
    | lia ]).
Qed.

Lemma proof_of_solver_entail_wit_2_30 : solver_entail_wit_2_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_30_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_30_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_31_split_goal_1 : solver_entail_wit_2_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_31_split_goal_2 : solver_entail_wit_2_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [lia |].
  assert (i = Zlength moves) as -> by lia.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_31 : solver_entail_wit_2_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_31_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_31_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_32_split_goal_1 : solver_entail_wit_2_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_32_split_goal_2 : solver_entail_wit_2_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [lia |].
  assert (i = Zlength moves) as -> by lia.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_32 : solver_entail_wit_2_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_32_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_32_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_33_split_goal_1 : solver_entail_wit_2_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as (_ & Hr & _ & _ & _ & Hbounds & _).
  specialize (Hbounds i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_33_split_goal_2 : solver_entail_wit_2_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hlt | Hge]; [lia |].
  assert (i = Zlength moves) as -> by lia.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  rewrite Znth0_cons in PreH30.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_33 : solver_entail_wit_2_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_33_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_33_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_34_split_goal_1 : solver_entail_wit_2_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PrefixWindow in PreH28.
  destruct PreH28 as
      [Hi_range [Hr [Hc [Hrow0 [Hcol0 [Hall
      [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]].
  specialize (Hall i ltac:(lia)).
  destruct Hall as [_ Hcol].
  rewrite <- Hc in Hcol.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_34_split_goal_2 : solver_entail_wit_2_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [exact Hi |].
  assert (i = Zlength moves) by lia. subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30. contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_34 : solver_entail_wit_2_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_34_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_34_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_35_split_goal_1 : solver_entail_wit_2_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength moves).
  {
    destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [exact Hi |].
    assert (i = Zlength moves) by lia. subst i.
    rewrite app_Znth2 in PreH30 by lia.
    replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
    simpl in PreH30. contradiction.
  }
  assert (Hright : Znth i moves 0 = 82).
  {
    rewrite app_Znth1 in PreH31, PreH32, PreH33 by lia.
    specialize (PreH11 i ltac:(lia)).
    destruct PreH11 as [[[Hleft | Hright] | Hdown] | Hup].
    - congruence.
    - exact Hright.
    - congruence.
    - congruence.
  }
  destruct (prefix_window_step_right_cases__right_valid_row
              moves i r c minr maxr minc maxc PreH28 Hi Hright)
    as [Hnewmax Hinside]; [lia |].
  apply Hnewmax. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_35_split_goal_2 : solver_entail_wit_2_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [exact Hi |].
  assert (i = Zlength moves) by lia. subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30. contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_35 : solver_entail_wit_2_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_35_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_35_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_36_split_goal_1 : solver_entail_wit_2_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i < Zlength moves).
  {
    destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [exact Hi |].
    assert (i = Zlength moves) by lia. subst i.
    rewrite app_Znth2 in PreH30 by lia.
    replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
    simpl in PreH30. contradiction.
  }
  assert (Hright : Znth i moves 0 = 82).
  {
    rewrite app_Znth1 in PreH31, PreH32, PreH33 by lia.
    specialize (PreH11 i ltac:(lia)).
    destruct PreH11 as [[[Hleft | Hright] | Hdown] | Hup].
    - congruence.
    - exact Hright.
    - congruence.
    - congruence.
  }
  destruct (prefix_window_step_right_cases__right_valid_row
              moves i r c minr maxr minc maxc PreH28 Hi Hright)
    as [Hnewmax Hinside]; [lia |].
  apply Hinside. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_36_split_goal_2 : solver_entail_wit_2_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [exact Hi |].
  assert (i = Zlength moves) by lia. subst i.
  rewrite app_Znth2 in PreH30 by lia.
  replace (Zlength moves - Zlength moves) with 0 in PreH30 by lia.
  simpl in PreH30. contradiction.
Qed.

Lemma proof_of_solver_entail_wit_2_36 : solver_entail_wit_2_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_36_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_36_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold WindowFits.
  split; assumption.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hiend : i = Zlength moves).
  { destruct (Z_lt_ge_dec i (Zlength moves)) as [Hi | Hi]; [| lia].
    rewrite Znth_app_left__termination_optimality in PreH26 by lia.
    specialize (PreH7 i ltac:(lia)).
    lia. }
  eapply optimal_prefix_at_end__termination_optimality; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply optimal_prefix_before_overflow__termination_optimality; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply optimal_prefix_before_overflow__termination_optimality; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_3_split_goal_2 : solver_entail_wit_4_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_3_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  remember (1 - minr) as rr eqn:Hrr.
  remember (1 - minc) as cc eqn:Hcc.
  Exists (rr, cc).
  split_pure_spatial.
  - cbn [fst snd].
    repeat rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_empty.
    cancel (CharArray.full s_pre (Zlength moves + 1) (moves +:: 0)).
    replace (row_pre + 0 * sizeof(INT)) with row_pre by lia.
    replace (col_pre + 0 * sizeof(INT)) with col_pre by lia.
    cancel (row_pre # Int |-> rr).
    cancel (col_pre # Int |-> cc).
    split_pure_spatial.
    + cancel emp.
    + split_pures; dump_pre_spatial; lia.
  - dump_pre_spatial.
    subst rr; subst cc.
    eapply optimal_window_realizes_spec__final_result
      with (maxr := maxr) (maxc := maxc).
    exact PreH22.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold IntArray.undef_full, store_undef_array.
  simpl.
  replace (row + 0) with row by lia.
  replace (col + 0) with col by lia.
  normalize.
  Intros_p Hrow_len.
  Intros_p Hcol_len.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_2_split_goal_spatial : solver_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold IntArray.full, store_array.
  simpl.
  replace (row + 0) with row by lia.
  replace (col + 0) with col by lia.
  normalize.
  Intros_p Hrow_len.
  Intros_p Hrow_tail.
  Intros_p Hcol_len.
  Intros_p Hcol_tail.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_2_split_goal_spatial.
Qed.
