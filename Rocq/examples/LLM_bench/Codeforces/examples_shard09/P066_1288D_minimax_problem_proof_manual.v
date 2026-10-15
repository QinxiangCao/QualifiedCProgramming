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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P066_1288D_minimax_problem_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P066_1288D_minimax_problem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib.
Local Open Scope sac.

Lemma proof_of_feasible_safety_wit_1_split_goal_1 : feasible_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hm : m_pre = 1 \/ m_pre = 2 \/ m_pre = 3 \/ m_pre = 4 \/
               m_pre = 5 \/ m_pre = 6 \/ m_pre = 7 \/ m_pre = 8) by lia.
  destruct Hm as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_1_split_goal_2 : feasible_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hm : m_pre = 1 \/ m_pre = 2 \/ m_pre = 3 \/ m_pre = 4 \/
               m_pre = 5 \/ m_pre = 6 \/ m_pre = 7 \/ m_pre = 8) by lia.
  destruct Hm as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_1 : feasible_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_feasible_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_feasible_safety_wit_2_split_goal_1 : feasible_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hm : m_pre = 1 \/ m_pre = 2 \/ m_pre = 3 \/ m_pre = 4 \/
               m_pre = 5 \/ m_pre = 6 \/ m_pre = 7 \/ m_pre = 8) by lia.
  destruct Hm as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_2_split_goal_2 : feasible_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hm : m_pre = 1 \/ m_pre = 2 \/ m_pre = 3 \/ m_pre = 4 \/
               m_pre = 5 \/ m_pre = 6 \/ m_pre = 7 \/ m_pre = 8) by lia.
  destruct Hm as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_2_split_goal_3 : feasible_safety_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_safety_wit_2_split_goal_4 : feasible_safety_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_safety_wit_2 : feasible_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_feasible_safety_wit_2_split_goal_2.
  - Goal_apply proof_of_feasible_safety_wit_2_split_goal_3.
  - Goal_apply proof_of_feasible_safety_wit_2_split_goal_4.
Qed.

Lemma proof_of_feasible_safety_wit_14_split_goal_1 : feasible_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hj : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
               j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct Hj as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_14_split_goal_2 : feasible_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hj : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
               j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct Hj as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma proof_of_feasible_safety_wit_14_split_goal_3 : feasible_safety_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_safety_wit_14_split_goal_4 : feasible_safety_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_safety_wit_14 : feasible_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_feasible_safety_wit_14_split_goal_2.
  - Goal_apply proof_of_feasible_safety_wit_14_split_goal_3.
  - Goal_apply proof_of_feasible_safety_wit_14_split_goal_4.
Qed.

Lemma proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [|k IH]; intros x lo hi; simpl.
    - Exists (@nil Z).
      simpl.
      split_pure_spatial.
      + Intros_p Hlohi.
        cancel.
      + Intros_p Hlohi2.
        split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l.
      Exists (a :: l).
      simpl.
      cancel.
  }
  assert (Hshape_full :
    forall x n,
      IntArray.full_shape x n
      |-- EX l : list Z, IntArray.full x n l).
  {
    intros x n.
    unfold IntArray.full_shape, IntArray.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full rep_pre 256).
  Intros reps.
  prop_apply_p (IntArray.full_Zlength rep_pre 256 reps).
  Intros_p Hreps_length.
  assert (Hm_cases :
    m_pre = 1 \/ m_pre = 2 \/ m_pre = 3 \/ m_pre = 4 \/
    m_pre = 5 \/ m_pre = 6 \/ m_pre = 7 \/ m_pre = 8) by lia.
  destruct Hm_cases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    Exists reps;
    split_pure_spatial.
  all: try (repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: reflexivity.
Qed.

Lemma proof_of_feasible_entail_wit_2_split_goal_1 : feasible_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_3_split_goal_1 : feasible_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH19 by lia.
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_3_split_goal_2 : feasible_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RepresentativePrefix.
  intros mask Hmask.
  left.
  split.
  - rewrite (Znth_indep reps_2 mask (-1) 0) by
        (rewrite Z.shiftl_1_l in PreH13; lia).
    apply PreH19.
    rewrite Z.shiftl_1_l in PreH13.
    lia.
  - intros row Hrow.
    lia.
Qed.

Lemma proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_4_split_goal_1 : feasible_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH20.
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_split_goal_2 : feasible_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RowMaskPrefix.
  split.
  - change (0 <= 0 < 1).
    lia.
  - intros c Hc.
    lia.
Qed.

Lemma proof_of_feasible_entail_wit_4_split_goal_3 : feasible_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_entail_wit_4 : feasible_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_5_1_split_goal_1 : feasible_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
    eapply row_mask_set_next__row_mask_step; eauto; lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_feasible_entail_wit_5_1_split_goal_2 : feasible_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
    pose proof (row_mask_set_next__row_mask_step
      rows x_pre i j mask ltac:(lia) PreH29 ltac:(lia)) as Hnext.
    unfold RowMaskPrefix in Hnext.
    destruct Hnext as [[_ Hmask_bound] _].
    rewrite Z.shiftl_1_l.
    assert (2 ^ (j + 1) <= 2 ^ m_pre).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_feasible_entail_wit_5_1_split_goal_3 : feasible_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.shiftl_1_l.
  rewrite signed_last_nbits_eq.
  - apply Z.lor_nonneg. split.
    + unfold RowMaskPrefix in PreH29. lia.
    + apply Z.pow_nonneg; lia.
  - lia.
  - split.
    + assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_lt_mono_r; lia.
Qed.

Lemma proof_of_feasible_entail_wit_5_1_split_goal_4 : feasible_entail_wit_5_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_entail_wit_5_1_split_goal_spatial : feasible_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) by lia.
  replace (a_pre + (i * m_pre + j) * sizeof(INT)) with
    ((a_pre + i * m_pre * sizeof(INT)) + j * sizeof(INT)) by nia.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full
    (a_pre + i * m_pre * sizeof(INT)) j m_pre
    (Znth j (Znth i rows (nil : list Z)) 0)
    (Znth i rows (nil : list Z))).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth.
    change ((IntArray2.ElemArray.full
      (IntArray2.row_addr a_pre m_pre i) m_pre
      (Znth i rows (nil : list Z)) **
      IntArray2.missing_i a_pre i 0 n_pre m_pre rows) |--
      IntArray2.full a_pre n_pre m_pre rows).
    sep_apply_l_atomic (IntArray2.missing_i_merge_to_full
      a_pre i n_pre m_pre rows (Znth i rows (nil : list Z))).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth.
      cancel.
Qed.

Lemma proof_of_feasible_entail_wit_5_1 : feasible_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_5_1_split_goal_spatial.
  - dump_pre_spatial.
    rewrite Z.shiftl_1_l.
    rewrite signed_last_nbits_eq.
    + rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
      eapply row_mask_set_next__row_mask_step; eauto; lia.
    + lia.
    + split.
      * assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
      * apply Z.pow_lt_mono_r; lia.
  - dump_pre_spatial.
    rewrite Z.shiftl_1_l.
    rewrite signed_last_nbits_eq.
    + rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
      pose proof (row_mask_set_next__row_mask_step
        rows x_pre i j mask ltac:(lia) PreH29 ltac:(lia)) as Hnext.
      unfold RowMaskPrefix in Hnext.
      destruct Hnext as [[_ Hmask_bound] _].
      rewrite Z.shiftl_1_l.
      assert (2 ^ (j + 1) <= 2 ^ m_pre).
      { apply Z.pow_le_mono_r; lia. }
      lia.
    + lia.
    + split.
      * assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
      * apply Z.pow_lt_mono_r; lia.
  - dump_pre_spatial.
    rewrite Z.shiftl_1_l.
    rewrite signed_last_nbits_eq.
    + apply Z.lor_nonneg. split.
      * unfold RowMaskPrefix in PreH29. lia.
      * apply Z.pow_nonneg; lia.
    + lia.
    + split.
      * assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
      * apply Z.pow_lt_mono_r; lia.
  - dump_pre_spatial. nia.
Qed.

Lemma proof_of_feasible_entail_wit_5_2_split_goal_1 : feasible_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
  eapply row_mask_clear_next__row_mask_step; eauto; lia.
Qed.

Lemma proof_of_feasible_entail_wit_5_2_split_goal_2 : feasible_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_feasible_entail_wit_5_2_split_goal_spatial : feasible_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) by lia.
  replace (a_pre + (i * m_pre + j) * sizeof(INT)) with
    ((a_pre + i * m_pre * sizeof(INT)) + j * sizeof(INT)) by nia.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full
    (a_pre + i * m_pre * sizeof(INT)) j m_pre
    (Znth j (Znth i rows (nil : list Z)) 0)
    (Znth i rows (nil : list Z))).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth.
    change ((IntArray2.ElemArray.full
      (IntArray2.row_addr a_pre m_pre i) m_pre
      (Znth i rows (nil : list Z)) **
      IntArray2.missing_i a_pre i 0 n_pre m_pre rows) |--
      IntArray2.full a_pre n_pre m_pre rows).
    sep_apply_l_atomic (IntArray2.missing_i_merge_to_full
      a_pre i n_pre m_pre rows (Znth i rows (nil : list Z))).
    + dump_pre_spatial. lia.
    + rewrite replace_Znth_Znth.
      cancel.
Qed.

Lemma proof_of_feasible_entail_wit_5_2 : feasible_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_5_2_split_goal_spatial.
  - dump_pre_spatial.
    rewrite (Znth_indep rows i __default__List_Z (nil : list Z)) in PreH3 by lia.
    eapply row_mask_clear_next__row_mask_step; eauto; lia.
  - dump_pre_spatial. nia.
Qed.

Lemma proof_of_feasible_entail_wit_6_1_split_goal_1 : feasible_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : (0 <= q /\ q <= full)%Z |- _ => rename H into Hq
  end.
  assert (Hmask_in : 0 <= mask < Zlength reps_2) by lia.
  assert (Hq_in : 0 <= q < Zlength reps_2) by lia.
  destruct (Z.eq_dec q mask) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by exact Hmask_in.
    lia.
  - rewrite (@Znth_replace_Znth_Diff Z 0 reps_2 mask q i
      Hmask_in Hq_in ltac:(lia)).
    specialize (PreH28 q Hq).
    lia.
Qed.

Lemma proof_of_feasible_entail_wit_6_1_split_goal_2 : feasible_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpow : 2 ^ m_pre = full + 1).
  { rewrite <- Z.shiftl_1_l. lia. }
  apply (representative_insert__representative_update
    rows x_pre m_pre i reps_2 mask).
  - lia.
  - lia.
  - lia.
  - lia.
  - exact PreH26.
  - rewrite <- (Znth_indep reps_2 mask 0 (-1)) by lia.
    specialize (PreH28 mask ltac:(lia)).
    lia.
  - assert (j = m_pre) by lia. subst j. exact PreH27.
Qed.

Lemma proof_of_feasible_entail_wit_6_1_split_goal_3 : feasible_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH25.
Qed.

Lemma proof_of_feasible_entail_wit_6_1 : feasible_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_6_1_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_6_2_split_goal_1 : feasible_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : (0 <= q /\ q <= full)%Z |- _ => rename H into Hq
  end.
  specialize (PreH28 q Hq).
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_6_2_split_goal_2 : feasible_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpow : 2 ^ m_pre = full + 1).
  { rewrite <- Z.shiftl_1_l. lia. }
  apply (representative_skip__representative_update
    rows x_pre m_pre i reps_2 mask).
  - lia.
  - lia.
  - exact PreH26.
  - rewrite <- (Znth_indep reps_2 mask 0 (-1)) by lia.
    lia.
  - assert (j = m_pre) by lia. subst j. exact PreH27.
Qed.

Lemma proof_of_feasible_entail_wit_6_2 : feasible_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_6_2_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_7_split_goal_1 : feasible_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : (0 <= q /\ q <= full)%Z |- _ => rename H into Hq
  end.
  specialize (PreH20 q Hq).
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_7_split_goal_2 : feasible_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold NoCoverPrefix.
  intros s u Hs Hu Hbefore Hsrep Hurep.
  lia.
Qed.

Lemma proof_of_feasible_entail_wit_7_split_goal_3 : feasible_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre) by lia. subst i.
  exact PreH19.
Qed.

Lemma proof_of_feasible_entail_wit_7 : feasible_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_feasible_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_feasible_entail_wit_8_split_goal_1 : feasible_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH22. exact H.
Qed.

Lemma proof_of_feasible_entail_wit_8 : feasible_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_8_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_9_1_split_goal_1 : feasible_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH25. exact H.
Qed.

Lemma proof_of_feasible_entail_wit_9_1_split_goal_2 : feasible_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH13.
  eapply no_cover_outer_missing__cover_search.
  - exact PreH24.
  - left. lia.
Qed.

Lemma proof_of_feasible_entail_wit_9_1 : feasible_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_feasible_entail_wit_9_1_split_goal_2.
Qed.

Lemma proof_of_feasible_entail_wit_9_2_split_goal_1 : feasible_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH14.
  eapply no_cover_outer_missing__cover_search.
  - exact PreH21.
  - right.
    rewrite (Znth_indep reps_2 s (-1) 0) by lia.
    exact PreH1.
Qed.

Lemma proof_of_feasible_entail_wit_9_2 : feasible_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_9_2_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_10_1_split_goal_1 : feasible_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH14.
  eapply no_cover_inner_missing__cover_search.
  - exact PreH25.
  - rewrite (Znth_indep reps_2 u (-1) 0) by lia.
    exact PreH1.
Qed.

Lemma proof_of_feasible_entail_wit_10_1 : feasible_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_feasible_entail_wit_10_2_split_goal_1 : feasible_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH15.
  eapply no_cover_inner_noncover__cover_search.
  - exact PreH26.
  - exact PreH1.
Qed.

Lemma proof_of_feasible_entail_wit_10_2 : feasible_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_feasible_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_feasible_return_wit_1_split_goal_1 : feasible_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (completed_no_cover_excludes_feasible__feasible_outcomes
    rows x_pre m_pre n_pre reps_2 s full).
  - lia.
  - exact PreH9.
  - rewrite (Znth_indep rows 0 (@nil Z) __default__List_Z) by lia.
    exact PreH10.
  - exact PreH13.
  - exact PreH19.
  - exact PreH20.
  - exact PreH1.
Qed.

Lemma proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_feasible_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.shiftl_1_l in PreH15.
  assert (Hsrange : 0 <= s < 2 ^ m_pre).
  { lia. }
  assert (Hurange : 0 <= u < 2 ^ m_pre).
  { lia. }
  destruct (PreH25 s Hsrange) as
    [[Hsminus _] | (si & Hsi & Hsrep & Hsmask)].
  - rewrite (Znth_indep reps_2 s (-1) 0) in Hsminus by lia.
    lia.
  - rewrite (Znth_indep reps_2 s (-1) 0) in Hsrep by lia.
    subst si.
    destruct (PreH25 u Hurange) as
      [[Huminus _] | (uj & Huj & Hurep & Humask)].
    + rewrite (Znth_indep reps_2 u (-1) 0) in Huminus by lia.
      lia.
    + rewrite (Znth_indep reps_2 u (-1) 0) in Hurep by lia.
      subst uj.
      Exists (Znth s reps_2 0) (Znth u reps_2 0) reps_2.
      split_pure_spatial.
      * unfold IntArray.full, store_array.
        simpl store_array_rec.
        replace (bi_pre + 0) with bi_pre by lia.
        replace (bj_pre + 0) with bj_pre by lia.
        LLM_pre_process ltac:(lia || nia || int_auto).
      * split_pures.
        -- dump_pre_spatial. lia.
        -- dump_pre_spatial. lia.
        -- dump_pre_spatial.
           apply (row_masks_cover_pair__feasible_outcomes rows x_pre m_pre
             (Znth s reps_2 0) (Znth u reps_2 0) s u).
           ++ rewrite (Znth_indep rows 0 (@nil Z) __default__List_Z) by lia.
              exact PreH12.
           ++ rewrite <- PreH11. exact Hsi.
           ++ rewrite <- PreH11. exact Huj.
           ++ exact Hsmask.
           ++ exact Humask.
           ++ rewrite Z.shiftl_1_l, <- PreH15. exact PreH1.
Qed.

Lemma proof_of_feasible_which_implies_wit_1 : feasible_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.mixed_full_to_undef_full bi_pre 1 old_bi).
  sep_apply_l_atomic (IntArray.mixed_full_to_undef_full bj_pre 1 old_bj).
  rewrite (IntArray.undef_full_unfold bi_pre 0 (@nil Z)) by lia.
  rewrite (IntArray.undef_full_unfold bj_pre 0 (@nil Z)) by lia.
  repeat rewrite IntArray.undef_seg_empty.
  replace (bi_pre + 0 * sizeof(INT)) with bi_pre by lia.
  replace (bj_pre + 0 * sizeof(INT)) with bj_pre by lia.
  cancel (bi_pre # Int |->_).
  cancel (bj_pre # Int |->_).
  cancel emp.
  cancel.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2) by
    (apply Z.div_pos; lia).
  assert (Hhalf_upper : (hi - lo + 1) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2) by
    (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_upper : (hi - lo + 1) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_pos : 1 <= (hi - lo + 1) / 2) by
    (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH1 ltac:(lia) PreH6 PreH7 PreH5). }
  pose proof (pair_at_least_zero__solver_semantics
    rows PreH1 Hentries ltac:(lia)) as Hpair0.
  destruct (optimal_pair_score_exists__solver_semantics
    rows PreH1 Hentries ltac:(lia))
    as [best Hoptimal].
  pose proof (optimal_pair_score_bounds__solver_semantics
    rows best PreH1 Hentries Hoptimal)
    as Hbest_bounds.
  assert (Hmeaning : SolverSearchMeaning rows 0 1000000000 0 0).
  { exists best. split; [exact Hoptimal |]. split; [lia | exact Hpair0]. }
  pose proof (PreH4 0 ltac:(lia)) as Hmbounds.
  Exists 0 0.
  split_pure_spatial.
  - repeat rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_empty.
    simpl.
    repeat rewrite Znth_cons by lia.
    replace (bi_pre + 0) with bi_pre by lia.
    replace (bj_pre + 0) with bj_pre by lia.
    repeat cancel.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH7 ltac:(lia)
      PreH12 PreH13 PreH14). }
  pose proof PreH3 as Hpair_bounds.
  destruct Hpair_bounds as [Hi [Hj Hcover]].
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) ÷ 2).
  { apply quot_nonnegative__solver_semantics; lia. }
  destruct PreH22 as [best [Hoptimal [[Hlobest Hbesthi] Hcurrent]]].
  pose proof (proj1 (feasible_threshold_optimal_bound__solver_semantics
    rows best (lo + (hi - lo + 1) ÷ 2) PreH7 Hentries Hoptimal)
    ltac:(exists i, j; exact PreH3)) as Hmidbest.
  assert (Hmeaning : SolverSearchMeaning rows
      (lo + (hi - lo + 1) ÷ 2) hi i j).
  { exists best. split; [exact Hoptimal |].
    split; [lia | exact PreH3]. }
  Exists j i.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_full_shape rep_pre 256 reps).
    repeat rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_empty.
    simpl.
    repeat rewrite Znth_cons by lia.
    replace (bi_pre + 0) with bi_pre by lia.
    replace (bj_pre + 0) with bj_pre by lia.
    replace (Znth 0 (i + 1 :: nil) 0) with (i + 1)
      by (rewrite Znth0_cons; reflexivity).
    replace (Znth 0 (j + 1 :: nil) 0) with (j + 1)
      by (rewrite Znth0_cons; reflexivity).
    repeat cancel.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH7 ltac:(lia)
      PreH12 PreH13 PreH14). }
  destruct PreH22 as [best [Hoptimal [[Hlobest Hbesthi] Hcurrent]]].
  pose proof (proj2 (feasible_threshold_optimal_bound__solver_semantics
    rows best (lo + (hi - lo + 1) ÷ 2) PreH7 Hentries Hoptimal) PreH3)
    as Hbestmid.
  pose proof (half_positive__solver_semantics (hi - lo + 1) ltac:(lia))
    as Hhalf_positive.
  pose proof (half_less_than_input__solver_semantics (hi - lo + 1) ltac:(lia))
    as Hhalf_small.
  assert (Hmeaning : SolverSearchMeaning rows lo
      (lo + (hi - lo + 1) ÷ 2 - 1) cur_i_2 cur_j_2).
  { exists best. split; [exact Hoptimal |].
    split; [lia | exact Hcurrent]. }
  Exists cur_j_2 cur_i_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_full_shape rep_pre 256 reps).
    cancel.
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH8 ltac:(lia)
      PreH13 PreH14 PreH15). }
  destruct PreH23 as [best [Hoptimal [[Hlobest Hbesthi] Hcurrent]]].
  assert (Hbest : best = 0) by lia.
  subst best.
  pose proof (optimal_pair_to_spec__solver_semantics
    rows 0 i j PreH8 Hentries Hoptimal PreH3) as Hspec.
  Exists (i + 1, j + 1).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_full_shape rep_pre 256 reps).
    simpl.
    cancel.
  - dump_pre_spatial. exact Hspec.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH8 ltac:(lia)
      PreH13 PreH14 PreH15). }
  exfalso.
  apply PreH3.
  exists 0, 0.
  eapply pair_at_least_zero__solver_semantics; eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hentries : MatrixEntriesBounded rows).
  { exact (matrix_entries_bounded_from_flat__solver_semantics
      rows n_pre m_pre __default__List_Z PreH3 ltac:(lia)
      PreH8 PreH9 PreH10). }
  destruct PreH18 as [best [Hoptimal [[Hlobest Hbesthi] Hcurrent]]].
  assert (Hbest : best = lo) by lia.
  subst best.
  pose proof (optimal_pair_to_spec__solver_semantics
    rows lo cur_i cur_j PreH3 Hentries Hoptimal Hcurrent) as Hspec.
  Exists (cur_i + 1, cur_j + 1).
  split_pure_spatial.
  - simpl. repeat cancel.
  - dump_pre_spatial. exact Hspec.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_1 : solver_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2) by
    (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_2 : solver_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf_upper : (hi - lo + 1) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_3 : solver_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_3.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_2 : solver_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_3 : solver_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_4 : solver_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_4.
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure_split_goal_1 : solver_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_7_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (IntArray.undef_full_unfold bi_pre 0 (@nil Z)) by lia.
  rewrite (IntArray.undef_full_unfold bj_pre 0 (@nil Z)) by lia.
  repeat rewrite IntArray.undef_seg_empty.
  replace (bi_pre + 0 * sizeof(INT)) with bi_pre by lia.
  replace (bj_pre + 0 * sizeof(INT)) with bj_pre by lia.
  normalize.
  cancel (bi_pre # Int |->_).
  cancel (bj_pre # Int |->_).
Qed.

Lemma proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (None :: nil) (None :: nil).
  split_pure_spatial.
  - repeat rewrite IntArray.mixed_full_unfold.
    cbn [IntArray.mixedstoreA].
    repeat rewrite IntArray.mixed_seg_empty.
    replace (&( "ci" ) + 0 * sizeof(INT)) with (&( "ci" )) by lia.
    replace (&( "cj" ) + 0 * sizeof(INT)) with (&( "cj" )) by lia.
    cancel (&( "ci" ) # Int |->_).
    cancel (&( "cj" ) # Int |->_).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_solver_which_implies_wit_3_split_goal_spatial : solver_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite !Zlength_correct in PreH1, PreH2, PreH3, PreH4.
  destruct ci_values as [|ci [|ci2 ci_tail]]; simpl in PreH1; try lia.
  destruct cj_values as [|cj [|cj2 cj_tail]]; simpl in PreH2; try lia.
  destruct old_is as [|oi [|oi2 oi_tail]]; simpl in PreH3; try lia.
  destruct old_js as [|oj [|oj2 oj_tail]]; simpl in PreH4; try lia.
  repeat rewrite IntArray.full_unfold.
  repeat rewrite IntArray.seg_empty.
  cbn [Znth].
  repeat match goal with
  | |- context [?p + 0 * sizeof(INT)] => replace (p + 0 * sizeof(INT)) with p by lia
  end.
  repeat rewrite Znth0_cons.
  Intros_p Hs1.
  Intros_p Hs2.
  Intros_p Hs3.
  Intros_p Hs4.
  normalize.
  cancel (&( "ci" ) # Int |-> ci).
  cancel (&( "cj" ) # Int |-> cj).
  cancel (bi_pre # Int |-> oi).
  cancel (bj_pre # Int |-> oj).
Qed.

Lemma proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.mixed_full_to_undef_full (&( "ci" )) 1 ci_values).
  sep_apply_l_atomic (IntArray.mixed_full_to_undef_full (&( "cj" )) 1 cj_values).
  rewrite (IntArray.undef_full_unfold (&( "ci" )) 0 (@nil Z)) by lia.
  rewrite (IntArray.undef_full_unfold (&( "cj" )) 0 (@nil Z)) by lia.
  repeat rewrite IntArray.undef_seg_empty.
  replace (&( "ci" ) + 0 * sizeof(INT)) with (&( "ci" )) by lia.
  replace (&( "cj" ) + 0 * sizeof(INT)) with (&( "cj" )) by lia.
  normalize.
  cancel (&( "ci" ) # Int |->_).
  cancel (&( "cj" ) # Int |->_).
Qed.

Lemma proof_of_solver_which_implies_wit_5 : solver_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (IntArray.full_Zlength bi_pre 1 bi_values).
  prop_apply_p (IntArray.full_Zlength bj_pre 1 bj_values).
  Intros_p Hbi.
  Intros_p Hbj.
  Exists (map (@Some Z) bj_values) (map (@Some Z) bi_values).
  split_pure_spatial.
  - sep_apply_r_atomic (IntArray.full_to_mixed_full bi_pre 1 bi_values).
    sep_apply_r_atomic (IntArray.full_to_mixed_full bj_pre 1 bj_values).
    cancel (IntArray.full bi_pre 1 bi_values).
    cancel (IntArray.full bj_pre 1 bj_values).
  - split_pures.
    + dump_pre_spatial.
      rewrite Zlength_correct, length_map, <- Zlength_correct.
      exact Hbi.
    + dump_pre_spatial.
      rewrite Zlength_correct, length_map, <- Zlength_correct.
      exact Hbj.
Qed.
