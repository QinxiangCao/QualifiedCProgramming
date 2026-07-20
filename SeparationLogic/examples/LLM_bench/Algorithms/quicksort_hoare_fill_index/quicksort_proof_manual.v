Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib MonotonicList VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_fill_index Require Import quicksort_goal.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_fill_index Require Import quicksort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.
Local Open Scope sac.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_hole_outer_inv, same_outside_range.
    rewrite replace_Znth_Znth by (rewrite PreH1; lia).
    repeat split; try lia; try reflexivity.
Qed.

Lemma proof_of_partition_entail_wit_3 : partition_entail_wit_3.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    eapply partition_hole_outer_scan_decrease_j; eauto.
    rewrite PreH4. exact PreH9.
Qed.

Lemma proof_of_partition_entail_wit_4 : partition_entail_wit_4.
Proof.
  pre_process.
  Exists (replace_Znth i (Znth j l1_2 0) l1_2).
  split_pure_spatial.
  - cancel.
  - entailer!.
    eapply partition_hole_outer_fill_left_to_left_scan; eauto.
    rewrite PreH5. exact PreH10.
Qed.

Lemma proof_of_partition_entail_wit_5 : partition_entail_wit_5.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    eapply partition_hole_left_scan_increase_i; eauto.
    rewrite PreH4. exact PreH9.
Qed.

Lemma proof_of_partition_entail_wit_6 : partition_entail_wit_6.
Proof.
  pre_process.
  Exists (replace_Znth j (Znth i l1_2 0) l1_2).
  split_pure_spatial.
  - cancel.
  - entailer!.
    eapply partition_hole_left_fill_right_to_outer; eauto.
    rewrite PreH5. exact PreH10.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth i pivot l1_2).
  split_pure_spatial.
  - cancel.
  - entailer!.
    + eapply partition_hole_outer_exit_yields_partitioned_at; eauto.
      rewrite PreH4. exact PreH9.
    + unfold partition_hole_outer_inv in PreH13.
      destruct PreH13 as [_ [Hsame _]].
      exact Hsame.
    + unfold partition_hole_outer_inv in PreH13.
      destruct PreH13 as [Hperm _].
      exact Hperm.
Qed.

Lemma proof_of_partition_return_wit_2 : partition_return_wit_2.
Proof.
  pre_process.
  Exists (replace_Znth i pivot l1_2).
  split_pure_spatial.
  - cancel.
  - entailer!.
    + eapply partition_hole_left_exit_yields_partitioned_at; eauto.
      rewrite PreH4. exact PreH9.
    + unfold partition_hole_left_scan_inv in PreH13.
      assert (Hij_eq : i = j) by lia.
      subst j.
      destruct PreH13 as [_ [Hsame _]].
      exact Hsame.
    + unfold partition_hole_left_scan_inv in PreH13.
      assert (Hij_eq : i = j) by lia.
      subst j.
      destruct PreH13 as [Hperm _].
      exact Hperm.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  pre_process.
  Exists l1_4.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n l1_4).
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
      assert (Hlen2 : Zlength l1_2 = n).
      { rewrite <- Hlen12. exact PreH14. }
      assert (Hlen3 : Zlength l1_3 = n).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hlen4 : Zlength l1_4 = n).
      { rewrite <- Hlen34. exact Hlen3. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact PreH5.
        - exact PreH17.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH19.
        - exact PreH13.
      }
      assert (Hpart4 : partitioned_at l1_4 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact PreH1.
        - exact PreH17.
        - exact (conj Hlen34 Heq34).
        - rewrite Hlen3. exact PreH19.
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
      * exact PreH17.
      * rewrite Hlen4. exact PreH19.
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
  - cancel (IntArray.full arr_pre n l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact PreH8.
      * exact PreH1.
    + dump_pre_spatial.
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
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH2 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n).
      { rewrite <- Hlen12. exact PreH11. }
      assert (Hlen3 : Zlength l1_3 = n).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact PreH1.
        - exact PreH14.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH16.
        - exact PreH10.
      }
      eapply quicksort_partition_combine_right_guard_local.
      * exact PreH14.
      * rewrite Hlen3. exact PreH16.
      * split; [exact PreH6 | exact PreH7].
      * lia.
      * exact Hpart3.
      * exact PreH3.
Qed.

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  pre_process.
  Exists l1_3.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact PreH8.
      * exact PreH2.
    + dump_pre_spatial.
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
      destruct PreH9 as [Hlen12 Heq12].
      destruct PreH3 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n).
      { rewrite <- Hlen12. exact PreH11. }
      assert (Hlen3 : Zlength l1_3 = n).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact PreH2.
        - exact PreH14.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact PreH16.
        - exact PreH10.
      }
      eapply quicksort_partition_combine_left_guard_local.
      * exact PreH14.
      * rewrite Hlen3. exact PreH16.
      * split; [exact PreH6 | exact PreH7].
      * lia.
      * exact Hpart3.
      * exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n l1_2).
  - split_pures.
    + dump_pre_spatial.
      exact PreH5.
    + dump_pre_spatial.
      exact PreH6.
    + dump_pre_spatial.
      assert (Hlen2 : Zlength l1_2 = n).
      {
        pose proof (Permutation_length PreH5) as Hperm_len.
        rewrite !Zlength_correct in *.
        lia.
      }
      eapply quicksort_partition_combine_short_local.
      * exact PreH11.
      * rewrite Hlen2. exact PreH13.
      * split; [exact PreH3 | exact PreH4].
      * lia.
      * lia.
      * exact PreH7.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_2_pure : quicksort_range_partial_solve_wit_2_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial.
    pose proof (Permutation_length PreH4) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_3_pure : quicksort_range_partial_solve_wit_3_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
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
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
  - dump_pre_spatial.
    pose proof (Permutation_length PreH5) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
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

Lemma proof_of_quicksort_return_wit_2 : quicksort_return_wit_2.
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
      apply (proj1 (mono_nondec_iff_increasing l)).
      unfold mono_nondec.
      intros i j Hi Hij Hj.
      rewrite PreH2 in Hj.
      lia.
    + dump_pre_spatial.
      lia.
Qed.
