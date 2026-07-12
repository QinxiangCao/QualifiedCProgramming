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
From SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort Require Import dual_loop_quicksort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort.dual_loop_quicksort_lib.
Local Open Scope sac.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_1 : partition_two_loop_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_outer_inv, same_outside_range.
    repeat split; try lia; try reflexivity.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_2 : partition_two_loop_entail_wit_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_3 : partition_two_loop_entail_wit_3.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_right_scan_inv in *.
    destruct PreH13 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
    intros k Hk.
    assert (j <= k) by lia.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + lia.
    + apply Hright. lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_4_1 : partition_two_loop_entail_wit_4_1.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_right_scan_inv in *.
    destruct PreH12 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_4_2 : partition_two_loop_entail_wit_4_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_right_scan_inv in *.
    destruct PreH13 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_5 : partition_two_loop_entail_wit_5.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv in *.
    destruct PreH13 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hmid [Hright [Hjlt Hieq]]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
    + intros k Hk.
      assert (k < i \/ k = i) as [Hlt | ->] by lia.
      * apply Hmid. lia.
      * exact PreH1.
    + intros Heq.
      subst.
      pose proof (Hjlt PreH2).
      lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_6_1 : partition_two_loop_entail_wit_6_1.
Proof.
  pre_process.
  Exists (replace_Znth j (Znth i l1_2 0)
            (replace_Znth i (Znth j l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel.
  - entailer!.
    lazymatch goal with
    | Hinv : partition_left_scan_inv _ _ _ _ _ _ _ |- _ =>
        let Hhigh1 := fresh "Hhigh1" in
        assert (Hhigh1 : high_pre < Zlength l) by
          match goal with
          | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
          end;
        eapply partition_swap_left_scan_to_outer_inv; eauto
    end.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_6_2 : partition_two_loop_entail_wit_6_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_outer_inv in *.
    destruct PreH13 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hmid [Hright [Hjlt Hieq]]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_return_wit_1 : partition_two_loop_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth i (Znth low_pre l1_2 0)
            (replace_Znth low_pre (Znth i l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel.
  - entailer!.
    + lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ =>
          let Hhigh1 := fresh "Hhigh1" in
          assert (Hhigh1 : high_pre < Zlength l) by
            match goal with
            | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
            end;
          eapply partition_outer_exit_swap_yields_partitioned_at; eauto
      end.
    + lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ =>
          let Htmp := fresh "Htmp" in
          pose proof Hinv as Htmp;
          destruct Htmp as [_ [Hsame _]];
          let Hsame0 := fresh "Hsame0" in
          pose proof Hsame as Hsame0;
          destruct Hsame as [Hlen _];
          eapply same_outside_range_trans_local;
          [ exact Hsame0
          | apply same_outside_range_swap_inside_local;
            try lia;
            rewrite <- Hlen;
            match goal with
            | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
            end ]
      end.
    + let Htmp := fresh "Htmp" in
      lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ => pose proof Hinv as Htmp
      end;
      destruct Htmp as [Hperm [Hsame _]];
      destruct Hsame as [Hlen _];
      destruct (Z.eq_dec low_pre i) as [Heq | Hneq].
      * subst i.
        rewrite replace_Znth_Znth by (rewrite Zlength_replace_Znth; rewrite <- Hlen; lia).
        rewrite replace_Znth_Znth by (rewrite <- Hlen; lia).
        exact Hperm.
      * eapply Permutation_trans.
        -- exact Hperm.
        -- apply swap_Znth_perm_local.
           rewrite <- Hlen.
           lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures; dump_pre_spatial.
    + apply Permutation_refl.
    + unfold same_outside_range.
      split; [reflexivity | intros; reflexivity].
    + unfold range_nondecreasing.
      intros i j Hi Hij Hj.
      assert (i = j) by lia.
      subst; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  pre_process.
  Exists l1_3.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact PreH8.
      * exact PreH2.
    + dump_pre_spatial.
      assert (Heqret : retval = right_pre) by lia.
      subst retval.
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH3 as [Hlen23 Heq23].
      split.
      * rewrite Hlen12. exact Hlen23.
      * intros k Hk Hout.
        rewrite (Heq23 k).
        -- apply Heq12. exact Hk. exact Hout.
        -- rewrite <- Hlen12. exact Hk.
        -- destruct Hout as [Hlt | Hgt].
           ++ left. lia.
           ++ right. lia.
    + dump_pre_spatial.
      assert (Heqret : retval = right_pre) by lia.
      subst retval.
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH3 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact PreH12. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre right_pre).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact PreH2.
        - exact PreH15.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH17.
        - exact PreH10.
      }
      eapply quicksort_partition_combine_left_only_local.
      * exact PreH15.
      * rewrite Hlen3. exact PreH17.
      * reflexivity.
      * exact Hpart3.
      * exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  pre_process.
  Exists l1_4.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_4).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact PreH11.
      * eapply Permutation_trans.
        -- exact PreH5.
        -- exact PreH1.
    + dump_pre_spatial.
      destruct PreH12 as [Hlen12 Heq12].
      destruct PreH6 as [Hlen23 Heq23].
      destruct PreH2 as [Hlen34 Heq34].
      assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
      {
        split.
        - exact Hlen23.
        - intros k Hk Hout.
          apply Heq23.
          + exact Hk.
          + destruct Hout as [Hlt | Hgt].
            * left. lia.
            * right. lia.
      }
      assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
      {
        split.
        - exact Hlen34.
        - intros k Hk Hout.
          apply Heq34.
          + exact Hk.
          + destruct Hout as [Hlt | Hgt].
            * left. lia.
            * right. lia.
      }
      eapply same_outside_range_trans_local.
      * exact (conj Hlen12 Heq12).
      * eapply same_outside_range_trans_local.
        -- exact Hsame23_full.
        -- exact Hsame34_full.
    + dump_pre_spatial.
      destruct PreH12 as [Hlen12 Heq12].
      destruct PreH6 as [Hlen23 Heq23].
      destruct PreH2 as [Hlen34 Heq34].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact PreH15. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hlen4 : Zlength l1_4 = n_pre).
      { rewrite <- Hlen34. exact Hlen3. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact PreH5.
        - exact PreH18.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH20.
        - exact PreH13.
      }
      assert (Hpart4 : partitioned_at l1_4 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact PreH1.
        - exact PreH18.
        - exact (conj Hlen34 Heq34).
        - rewrite Hlen3. exact PreH20.
        - exact Hpart3.
      }
      assert (Hleft4 : range_nondecreasing l1_4 left_pre (retval - 1)).
      {
        eapply range_nondecreasing_ext_local.
        - exact Hlen34.
        - intros k Hk.
          assert (Hklen : 0 <= k < Zlength l1_3).
          { rewrite Hlen3. lia. }
          apply Heq34.
          + exact Hklen.
          + left. lia.
        - exact PreH7.
      }
      eapply quicksort_partition_combine_both_sides_local.
      * exact PreH18.
      * rewrite Hlen4. exact PreH20.
      * split; [exact PreH9 | exact PreH10].
      * exact Hpart4.
      * exact Hleft4.
      * exact PreH3.
Qed.

Lemma proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Proof.
  pre_process.
  Exists l1_3.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact PreH8.
      * exact PreH1.
    + dump_pre_spatial.
      assert (Heqret : retval = left_pre) by lia.
      subst retval.
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH2 as [Hlen23 Heq23].
      split.
      * rewrite Hlen12. exact Hlen23.
      * intros k Hk Hout.
        rewrite (Heq23 k).
        -- apply Heq12. exact Hk. exact Hout.
        -- rewrite <- Hlen12. exact Hk.
        -- destruct Hout as [Hlt | Hgt].
           ++ left. lia.
           ++ right. lia.
    + dump_pre_spatial.
      assert (Heqret : retval = left_pre) by lia.
      subst retval.
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH2 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact PreH12. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre left_pre).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact PreH1.
        - exact PreH15.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH17.
        - exact PreH10.
      }
      eapply quicksort_partition_combine_right_only_local.
      * exact PreH15.
      * rewrite Hlen3. exact PreH17.
      * reflexivity.
      * exact Hpart3.
      * exact PreH3.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_2_pure : quicksort_range_partial_solve_wit_2_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_length PreH4) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_3_pure : quicksort_range_partial_solve_wit_3_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_length PreH8) as Hlen_l_l2.
    pose proof (Permutation_length PreH2) as Hlen_l2_l1.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_4_pure : quicksort_range_partial_solve_wit_4_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_length PreH5) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_dual_loop_quicksort_return_wit_2 : dual_loop_quicksort_return_wit_2.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      apply Permutation_refl.
    + dump_pre_spatial.
      assert (Hn0 : n_pre = 0) by lia.
      rewrite Hn0 in PreH2.
      apply Zlength_nil_inv in PreH2.
      subst l.
      unfold increasing.
      auto.
    + dump_pre_spatial.
      lia.
Qed.

Lemma proof_of_dual_loop_quicksort_return_wit_1 : dual_loop_quicksort_return_wit_1.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - assert (Hlen1_2 : Zlength l1_2 = n_pre).
    {
      pose proof (Permutation_length PreH1) as Hperm_len.
      rewrite !Zlength_correct in *.
      lia.
    }
    split_pures.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      rewrite <- Hlen1_2 in PreH3.
      apply range_nondecreasing_full_to_increasing.
      exact PreH3.
    + dump_pre_spatial.
      exact Hlen1_2.
Qed.
