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
From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_goal.
From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray.mixed_full IntArray.mixed_seg.

Lemma scratch_full_tail_undef : forall x k cap l,
  0 <= k <= cap ->
  IntArray.full x k l ** IntArray.undef_seg x k cap |-- IntArray.undef_full x cap.
Proof.
  intros x k cap l Hk.
  sep_apply (IntArray.full_to_undef_full x k l).
  sep_apply (IntArray.undef_full_to_undef_seg x k).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 k cap Hk).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (cap - 0) with cap by lia. entailer!.
Qed.
Lemma scratch_undef_full_split : forall x k cap,
  0 <= k <= cap ->
  IntArray.undef_full x cap |-- IntArray.undef_full x k ** IntArray.undef_seg x k cap.
Proof.
  intros x k cap Hk.
  sep_apply (IntArray.undef_full_split_to_undef_seg x k cap Hk).
  sep_apply (IntArray.undef_seg_to_undef_full x 0 k).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (k - 0) with k by lia. entailer!.
Qed.

Require Import AUXLib.MonotonicList.

Lemma knapsack_Forall_read_default : forall (P : Z -> Prop) l k,
  Forall P l -> P 0 -> P (Znth k l 0).
Proof.
  intros P l k HFor Hzero.
  unfold Znth.
  destruct (nth_in_or_default (Z.to_nat k) l 0) as [Hin | Heq].
  - rewrite Forall_forall in HFor. apply HFor. exact Hin.
  - rewrite Heq. assumption.
Qed.

Ltac scratch_cancel :=
  elim_emp; sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end; try cancel.







































Lemma proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1 : zeroOneKnapsack_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (knapsack_Forall_read_default _ _
    ((((i - 1) * width) + (j - Znth (i - 1) weights_l 0)) - 0)
    PreH43 ltac:(lia)) as Hprev_lo.
  pose proof (knapsack_Forall_read_default _ _
    ((((i - 1) * width) + (j - Znth (i - 1) weights_l 0)) - 0)
    PreH44 ltac:(lia)) as Hprev_hi.
  pose proof (knapsack_Forall_read_default _ _ (i - 1) PreH41 ltac:(lia)) as Hv_lo.
  pose proof (knapsack_Forall_read_default _ _ (i - 1) PreH42 ltac:(lia)) as Hv_hi.
  lia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2 : zeroOneKnapsack_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  pose proof (knapsack_Forall_read_default _ _
    ((((i - 1) * width) + (j - Znth (i - 1) weights_l 0)) - 0)
    PreH43 ltac:(lia)) as Hprev_lo.
  pose proof (knapsack_Forall_read_default _ _
    ((((i - 1) * width) + (j - Znth (i - 1) weights_l 0)) - 0)
    PreH44 ltac:(lia)) as Hprev_hi.
  pose proof (knapsack_Forall_read_default _ _ (i - 1) PreH41 ltac:(lia)) as Hv_lo.
  pose proof (knapsack_Forall_read_default _ _ (i - 1) PreH42 ltac:(lia)) as Hv_hi.
  lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_4_split_goal_1 : zeroOneKnapsack_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 : zeroOneKnapsack_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hnonneg : Forall (Z.le 0) weights_l).
  { eapply Forall_impl; [|exact PreH38]. intros x Hx. lia. }
  pose proof (knapsack_Forall_read_default _ _ (i - 1) Hnonneg ltac:(lia)) as Hw0.
  assert (Hcap : 0 <= capacity_pre) by lia.
  clear - Hw0 Hcap. nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 : zeroOneKnapsack_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (i < n_pre + 1) by lia.
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1.
Proof.
  unfold zeroOneKnapsack_entail_wit_1; left; intros.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("dp")) ((n_pre+1)*(capacity_pre+1)) 90601 ltac:(nia)).
  Exists (@nil Z).
  replace (0*(capacity_pre+1)) with 0 by ring.
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption; try constructor.
    unfold KnapsackRowsDone, KnapsackTablePrefix.
    intros row col Hrow Hcol Hidx. unfold KnapsackCellIndex in Hidx. nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  Exists dp_l_2.
  split_pure_spatial.
  - replace (i * width + 0) with (i * width) by lia.
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg (&("dp")) 0 (i * width) dp_l_2).
    derivable1_refl_tac.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply KnapsackRowsDone_to_RowProgress0; assumption.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_1 : zeroOneKnapsack_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_Zlength weights_pre n_pre weights_l).
  Intros_p Hweights_len.
  prop_apply_p (IntArray.full_Zlength values_pre n_pre values_l).
  Intros_p Hvalues_len.
  assert (Hweights_bound : forall k, 0 <= k < n_pre -> 1 <= Znth k weights_l 0).
  { intros k Hk. eapply (proj1 (Forall_Znth (Z.le 1) 0 weights_l));
      [eassumption|lia]. }
  assert (Hvalues_bound : forall k, 0 <= k < n_pre -> 0 <= Znth k values_l 0 <= 10000).
  { intros k Hk. split.
    - eapply (proj1 (Forall_Znth (Z.le 0) 0 values_l)); [eassumption|lia].
    - apply Z.ge_le.
      eapply (proj1 (Forall_Znth (Z.ge 10000) 0 values_l)); [eassumption|lia]. }
  assert (Hcell : KnapsackCellCorrect weights_l values_l i j 0).
  { subst i. apply KnapsackCellCorrect_row0_zero; lia. }
  assert (Hcell_bound : 0 <= (0 : Z) <= 4000000) by lia.
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (i * width + j + 1)
    (dp_l_2 ++ 0 :: nil)).
  Intros_p Hdp_written.
  rewrite Zlength_app_cons in Hdp_written.
  all: Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - replace (i * width + (j + 1)) with (i * width + j + 1) by lia.
    solve [scratch_cancel].
  - split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (apply Forall_app; split; [assumption|constructor; [lia|constructor]]).
  all: eapply KnapsackRowProgress_append_cell_recurrence; try eassumption; try lia.
  all: nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_2 : zeroOneKnapsack_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_Zlength weights_pre n_pre weights_l).
  Intros_p Hweights_len.
  prop_apply_p (IntArray.full_Zlength values_pre n_pre values_l).
  Intros_p Hvalues_len.
  assert (Hweights_bound : forall k, 0 <= k < n_pre -> 1 <= Znth k weights_l 0).
  { intros k Hk. eapply (proj1 (Forall_Znth (Z.le 1) 0 weights_l));
      [eassumption|lia]. }
  assert (Hvalues_bound : forall k, 0 <= k < n_pre -> 0 <= Znth k values_l 0 <= 10000).
  { intros k Hk. split.
    - eapply (proj1 (Forall_Znth (Z.le 0) 0 values_l)); [eassumption|lia].
    - apply Z.ge_le.
      eapply (proj1 (Forall_Znth (Z.ge 10000) 0 values_l)); [eassumption|lia]. }
  assert (Hcell : KnapsackCellCorrect weights_l values_l i j 0).
  { subst j. apply KnapsackCellCorrect_col0_zero; try lia.
    intros k Hk. apply Hweights_bound; lia. }
  assert (Hcell_bound : 0 <= (0 : Z) <= 4000000) by lia.
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (i * width + j + 1)
    (dp_l_2 ++ 0 :: nil)).
  Intros_p Hdp_written.
  rewrite Zlength_app_cons in Hdp_written.
  all: Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - replace (i * width + (j + 1)) with (i * width + j + 1) by lia.
    solve [scratch_cancel].
  - split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (apply Forall_app; split; [assumption|constructor; [lia|constructor]]).
  all: eapply KnapsackRowProgress_append_cell_recurrence; try eassumption; try lia.
  all: nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_3 : zeroOneKnapsack_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_Zlength weights_pre n_pre weights_l).
  Intros_p Hweights_len.
  prop_apply_p (IntArray.full_Zlength values_pre n_pre values_l).
  Intros_p Hvalues_len.
  assert (Hweights_bound : forall k, 0 <= k < n_pre -> 1 <= Znth k weights_l 0).
  { intros k Hk. eapply (proj1 (Forall_Znth (Z.le 1) 0 weights_l));
      [eassumption|lia]. }
  assert (Hvalues_bound : forall k, 0 <= k < n_pre -> 0 <= Znth k values_l 0 <= 10000).
  { intros k Hk. split.
    - eapply (proj1 (Forall_Znth (Z.le 0) 0 values_l)); [eassumption|lia].
    - apply Z.ge_le.
      eapply (proj1 (Forall_Znth (Z.ge 10000) 0 values_l)); [eassumption|lia]. }
  all: assert (Hweight_positive :
      1 <= Znth (i - 1) weights_l 0) by
    (apply Hweights_bound; lia).
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hprevious :
      KnapsackCellCorrect weights_l values_l (i - 1)
        (j - Znth (i - 1) weights_l 0)
        (Znth ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1)
          (j - Znth (i - 1) weights_l 0)) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
         Znth (i - 1) values_l 0)) by
    (eapply KnapsackCellCorrect_take_better
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0)
            (without := Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)
            (prev := Znth ((((i - 1) * width) +
              (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
         Znth (i - 1) values_l 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
           Znth (i - 1) values_l 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (i * width + j + 1)
    (dp_l_2 ++ (Znth ((((i - 1) * width) +
       (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
     Znth (i - 1) values_l 0) :: nil)).
  Intros_p Hdp_written.
  rewrite Zlength_app_cons in Hdp_written.
  all: Exists (dp_l_2 ++
    (Znth ((((i - 1) * width) +
       (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
     Znth (i - 1) values_l 0) :: nil).
  split_pure_spatial.
  - replace (i * width + (j + 1)) with (i * width + j + 1) by lia.
    first [solve [scratch_cancel] |
      match goal with |- ?G => idtac "SPATIAL REMAINS" G end;
      fail 1 "unclosed spatial"].
  - split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (apply Forall_app; split; [assumption|constructor; [lia|constructor]]).
  all: eapply KnapsackRowProgress_append_cell_recurrence; try eassumption; try lia.
  all: nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_4 : zeroOneKnapsack_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_Zlength weights_pre n_pre weights_l).
  Intros_p Hweights_len.
  prop_apply_p (IntArray.full_Zlength values_pre n_pre values_l).
  Intros_p Hvalues_len.
  assert (Hweights_bound : forall k, 0 <= k < n_pre -> 1 <= Znth k weights_l 0).
  { intros k Hk. eapply (proj1 (Forall_Znth (Z.le 1) 0 weights_l));
      [eassumption|lia]. }
  assert (Hvalues_bound : forall k, 0 <= k < n_pre -> 0 <= Znth k values_l 0 <= 10000).
  { intros k Hk. split.
    - eapply (proj1 (Forall_Znth (Z.le 0) 0 values_l)); [eassumption|lia].
    - apply Z.ge_le.
      eapply (proj1 (Forall_Znth (Z.ge 10000) 0 values_l)); [eassumption|lia]. }
  all: assert (Hweight_positive :
      1 <= Znth (i - 1) weights_l 0) by
    (apply Hweights_bound; lia).
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hprevious :
      KnapsackCellCorrect weights_l values_l (i - 1)
        (j - Znth (i - 1) weights_l 0)
        (Znth ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1)
          (j - Znth (i - 1) weights_l 0)) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (eapply KnapsackCellCorrect_keep_without_when_better_or_equal
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0)
            (prev := Znth ((((i - 1) * width) +
              (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (i * width + j + 1)
    (dp_l_2 ++ Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil)).
  Intros_p Hdp_written.
  rewrite Zlength_app_cons in Hdp_written.
  all: Exists (dp_l_2 ++
    Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil).
  split_pure_spatial.
  - replace (i * width + (j + 1)) with (i * width + j + 1) by lia.
    solve [scratch_cancel].
  - split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (apply Forall_app; split; [assumption|constructor; [lia|constructor]]).
  all: eapply KnapsackRowProgress_append_cell_recurrence; try eassumption; try lia.
  all: nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_5 : zeroOneKnapsack_entail_wit_6_5.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_Zlength weights_pre n_pre weights_l).
  Intros_p Hweights_len.
  prop_apply_p (IntArray.full_Zlength values_pre n_pre values_l).
  Intros_p Hvalues_len.
  assert (Hweights_bound : forall k, 0 <= k < n_pre -> 1 <= Znth k weights_l 0).
  { intros k Hk. eapply (proj1 (Forall_Znth (Z.le 1) 0 weights_l));
      [eassumption|lia]. }
  assert (Hvalues_bound : forall k, 0 <= k < n_pre -> 0 <= Znth k values_l 0 <= 10000).
  { intros k Hk. split.
    - eapply (proj1 (Forall_Znth (Z.le 0) 0 values_l)); [eassumption|lia].
    - apply Z.ge_le.
      eapply (proj1 (Forall_Znth (Z.ge 10000) 0 values_l)); [eassumption|lia]. }
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (eapply KnapsackCellCorrect_too_heavy
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (i * width + j + 1)
    (dp_l_2 ++ Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil)).
  Intros_p Hdp_written.
  rewrite Zlength_app_cons in Hdp_written.
  all: Exists (dp_l_2 ++
    Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil).
  split_pure_spatial.
  - replace (i * width + (j + 1)) with (i * width + j + 1) by lia.
    solve [scratch_cancel].
  - split_pures; dump_pre_spatial; try lia; try assumption.
  all: try (apply Forall_app; split; [assumption|constructor; [lia|constructor]]).
  all: eapply KnapsackRowProgress_append_cell_recurrence; try eassumption; try lia.
  all: nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7 : zeroOneKnapsack_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hj_end : j = capacity_pre + 1) by lia.
  Exists dp_l_2.
  split_pure_spatial.
  - replace ((i + 1) * width) with (i * width + j) by nia.
    repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    eapply KnapsackRowProgress_end_to_RowsDone; eassumption.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: assert (Hi_end : i = n_pre + 1) by lia.
  assert (Hresult : KnapsackMaxValue weights_l values_l n_pre capacity_pre
    (Znth (n_pre * width + capacity_pre) dp_l_2 0)).
  { replace (n_pre * width + capacity_pre) with
      (KnapsackCellIndex capacity_pre n_pre capacity_pre) by
      (unfold KnapsackCellIndex; nia).
    eapply KnapsackRowsDone_lookup_cell; try eassumption; try lia.
    unfold KnapsackCellIndex. nia. }
  all: Exists dp_l_2.
  all: split_pure_spatial.
  all: try (subst i;
            replace ((n_pre + 1) * width) with
              ((n_pre + 1) * (capacity_pre + 1)) by nia;
            rewrite IntArray.undef_seg_empty;
            sep_apply (IntArray.seg_to_full (&("dp")) 0
              ((n_pre + 1) * (capacity_pre + 1)) dp_l_2);
            replace ((&("dp")) + 0 * sizeof (INT)) with (&("dp")) by lia;
            replace ((n_pre + 1) * (capacity_pre + 1) - 0) with
              ((n_pre + 1) * (capacity_pre + 1)) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption; try (timeout 2 nia).
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
Proof.
  unfold zeroOneKnapsack_entail_wit_9; right; intros.
  apply scratch_full_tail_undef. nia.
Qed.
