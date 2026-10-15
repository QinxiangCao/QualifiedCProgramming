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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P049_411B_multi_core_processor_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P049_411B_multi_core_processor_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P049_411B_multi_core_processor_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (writer_count_increment_bound__direct_scan_step
    ins locks (j + 1) i k_pre counts
    (Znth j (Znth i xrows __default__List_Z) 0) PreH24 ltac:(lia))
    as Hbound.
  replace (Znth j (Znth i xrows __default__List_Z) 0 - 0)
    with (Znth j (Znth i xrows __default__List_Z) 0) by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (writer_count_increment_bound__direct_scan_step
    ins locks (j + 1) i k_pre counts
    (Znth j (Znth i xrows __default__List_Z) 0) PreH24 ltac:(lia))
    as Hbound.
  replace (Znth j (Znth i xrows __default__List_Z) 0 - 0)
    with (Znth j (Znth i xrows __default__List_Z) 0) by lia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH12 r_2 H).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH8 q H).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(unfold repeat_Z; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply dead_cells_through_zero__solver_init.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    reflexivity.
  - unfold repeat_Z.
    rewrite Znth_repeat.
    reflexivity.
  - lia.
  - intros cell Hcell.
    unfold repeat_Z.
    rewrite Znth_repeat.
    reflexivity.
  - intros core Hcore.
    unfold repeat_Z.
    rewrite Znth_repeat.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply lock_times_through_zero__solver_init.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    lia.
  - intros core Hcore.
    unfold repeat_Z.
    rewrite Znth_repeat.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH13 r_2 H).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_5 : solver_entail_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH9 q H).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace 105 with (104 + 1) at 1 by lia.
  rewrite (IntArray.undef_full_unfold (&( "writers" )) 104 (@nil Z)) by lia.
  replace ((&( "writers" )) + 0 * sizeof(INT)) with (&( "writers" )) by lia.
  sep_apply_l_atomic (valid_undef_store_int (&( "writers" ))).
  Intros_p Hvalid.
  dump_pre_spatial.
  unfold isvalidptr_int in Hvalid.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : forall p,
    p # Int |->_ |-- UCharArray.undef_full p 4).
  {
    intros p.
    unfold undef_store_int, UCharArray.undef_full, store_undef_array.
    simpl.
    Intros_p Hvalid.
    unfold store_4byte_noninit, undef_store_uchar, isvalidptr_char.
    normalize.
    split_pure_spatial.
    - replace (p + 0) with p by lia. cancel.
    - split_pures; dump_pre_spatial; unfold isvalidptr_int in Hvalid; lia.
  }
  assert (Harray : forall p (n : nat),
    IntArray.undef_full p (Z.of_nat n) |--
    UCharArray.undef_full p (4 * Z.of_nat n)).
  {
    intros p n. revert p.
    induction n as [|n IH]; intros p.
    - simpl. rewrite IntArray.undef_full_empty.
      rewrite UCharArray.undef_full_empty. cancel.
    - rewrite Nat2Z.inj_succ.
      rewrite (IntArray.undef_full_unfold p (Z.of_nat n) (@nil Z)) by lia.
      sep_apply_l_atomic
        (IntArray.undef_seg_to_undef_full p 1 (Z.succ (Z.of_nat n))).
      replace (p + 0 * sizeof(INT)) with p by lia.
      sep_apply_l_atomic (Hcell p).
      try rewrite sizeof_int in *.
      try rewrite sizeof_uchar in *.
      replace (p + 1 * 4) with (p + 4) by lia.
      replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia.
      sep_apply_l_atomic (IH (p + 4)).
      replace (4 * Z.succ (Z.of_nat n)) with (4 + 4 * Z.of_nat n) by lia.
      sep_apply_r_atomic
        (UCharArray.undef_full_merge_to_undef_full
          p 4 (4 + 4 * Z.of_nat n)).
      + dump_pre_spatial. pose proof (Nat2Z.is_nonneg n). lia.
      + replace (p + 4 * 1) with (p + 4) by lia.
        replace (4 + 4 * Z.of_nat n - 4) with (4 * Z.of_nat n) by lia.
        cancel.
      rewrite sizeof_uchar.
      replace (p + 4 * 1) with (p + 4) by lia.
      cancel.
  }
  sep_apply_l_atomic
    (IntArray.undef_full_split_to_undef_seg
      (&( "writers" )) (k_pre + 1) 105 ltac:(lia)).
  sep_apply_l_atomic
    (IntArray.undef_seg_to_undef_full
      (&( "writers" )) 0 (k_pre + 1)).
  replace ((&( "writers" )) + 0 * sizeof(INT)) with (&( "writers" )) by lia.
  replace (k_pre + 1 - 0) with (Z.of_nat (Z.to_nat (k_pre + 1))) by lia.
  sep_apply_l_atomic
    (Harray (&( "writers" )) (Z.to_nat (k_pre + 1))).
  replace (Z.of_nat (Z.to_nat (k_pre + 1))) with (k_pre + 1) by lia.
  rewrite sizeof_int.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hblock : forall p,
    aligned_4 p ->
    UCharArray.full p 4 (repeat 0 4%nat) |--
    IntArray.full p 1 (repeat 0 1%nat)).
  {
    intros p Halign.
    unfold UCharArray.full, IntArray.full, store_array.
    unfold StoreUCharAsElement.storeA, StoreIntAsElement.storeA.
    rewrite sizeof_int, sizeof_uchar.
    cbn.
    replace (p + 0) with p by lia.
    rewrite store_int_store_char.
    Exists 0 0 0 0.
    unfold store_char, store_uchar.
    normalize.
    split_pure_spatial.
    - Intros_p H4. Intros_p Hnil.
      Intros_p Hp0. Intros_p Hp1. Intros_p Hp2. Intros_p Hp3.
      cancel (store_byte p 0).
      cancel (store_byte (p + 1) 0).
      cancel (store_byte (p + 2) 0).
      cancel (store_byte (p + 3) 0).
    - Intros_p H4'. Intros_p Hnil'.
      Intros_p Hp0'. Intros_p Hp1'. Intros_p Hp2'. Intros_p Hp3'.
      split_pures.
      all: dump_pre_spatial.
      all: try (unfold merge_int; reflexivity).
      all: try int_auto.
      all: try tauto.
      all: auto.
      all: vm_compute.
      all: discriminate.
  }
  assert (Harray : forall (n : nat) p,
    aligned_4 p ->
    UCharArray.full p (4 * Z.of_nat n) (repeat 0 (4 * n)%nat) |--
    IntArray.full p (Z.of_nat n) (repeat 0 n)).
  {
    induction n as [|n IH]; intros p Halign.
    - unfold UCharArray.full, IntArray.full, store_array.
      cbn. Intros_p Hzero. Intros_p Hnil.
      split_pure_spatial.
      + cancel emp.
      + split_pures; dump_pre_spatial; auto.
    - replace (repeat 0 (4 * S n)%nat)
        with (repeat 0 4%nat ++ repeat 0 (4 * n)%nat).
      2:{ rewrite <- repeat_app. f_equal. lia. }
      replace (repeat 0 (S n)) with (0 :: repeat 0 n) by reflexivity.
      sep_apply_l_atomic
        (UCharArray.full_to_seg p (4 * Z.of_nat (S n))
          (repeat 0 4%nat ++ repeat 0 (4 * n)%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_split_to_seg p 0 4 (4 * Z.of_nat (S n))
          (repeat 0 4%nat ++ repeat 0 (4 * n)%nat) ltac:(lia)).
      replace (4 - 0) with (Zlength (repeat 0 4%nat)) by
        (rewrite Zlength_correct, repeat_length; lia).
      rewrite sublist_app_exact1.
      rewrite (sublist_split_app_r (Zlength (repeat 0 4%nat))
        (4 * Z.of_nat (S n) - 0) 4
        (repeat 0 4%nat) (repeat 0 (4 * n)%nat)) by
          (rewrite Zlength_correct, repeat_length; lia).
      replace (4 * Z.of_nat (S n) - 4) with (4 * Z.of_nat n) by lia.
      rewrite sublist_self by
        (rewrite Zlength_correct, repeat_length; lia).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 0 4 (repeat 0 4%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 4 (4 * Z.of_nat (S n))
          (repeat 0 (4 * n)%nat)).
      replace (p + 0 * sizeof(UCHAR)) with p by
        (rewrite sizeof_uchar; lia).
      replace (p + 4 * sizeof(UCHAR)) with (p + 4) by
        (rewrite sizeof_uchar; lia).
      sep_apply_l_atomic (Hblock p Halign).
      assert (Halign4 : aligned_4 (p + 4)).
      {
        unfold aligned_4 in *.
        rewrite Z.add_mod by lia.
        rewrite Halign.
        reflexivity.
      }
      replace (4 * Z.of_nat (S n) - 4) with (4 * Z.of_nat n) by lia.
      sep_apply_l_atomic (IH (p + 4) Halign4).
      pose proof
        (IntArray.full_merge_to_full p 1 (Z.of_nat (S n))
          (repeat 0 1%nat) (repeat 0 n) ltac:(lia)) as Hmerge.
      replace (p + 1 * sizeof(INT)) with (p + 4) in Hmerge by
        (rewrite sizeof_int; lia).
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in Hmerge by lia.
      sep_apply Hmerge.
      cbn. reflexivity.
  }
  replace ((&( "writers" )) + 0 * sizeof(INT)) with (&( "writers" )) in PreH18 by lia.
  pose proof
    (Harray (Z.to_nat (k_pre + 1)) (&( "writers" )) PreH18) as Hwhole.
  replace (Z.of_nat (Z.to_nat (k_pre + 1))) with (k_pre + 1) in Hwhole by lia.
  unfold repeat_Z.
  rewrite sizeof_int.
  replace ((&( "writers" )) + 0 * 4) with (&( "writers" )) by lia.
  replace (Z.to_nat (4 * (k_pre + 1)))
    with (4 * Z.to_nat (k_pre + 1))%nat by lia.
  sep_apply_l_atomic Hwhole.
  sep_apply_l_atomic
    (IntArray.full_to_seg (&( "writers" )) (k_pre + 1)
      (repeat 0 (Z.to_nat (k_pre + 1)))).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_spatial : solver_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (IntArray.undef_full_split_to_undef_seg (&( "first" )) 1 105 ltac:(lia)).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- (repeat_Z_tail (-1) (c - 1)) by lia.
  f_equal.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hc : c = k_pre + 1) by lia.
  subst c.
  pose proof
    (lock_times_before_succ_eq__scan_entry ins locks_2 j PreH14 PreH18)
    as Hbefore.
  assert (Hdead : DeadCellsBefore ins locks_2 k_pre (j + 1) dead_2).
  { unfold DeadCellsBefore. rewrite Hbefore.
    replace (j + 1 - 1) with j by lia. exact PreH19. }
  pose proof (direct_lock_scan_zero__scan_entry ins locks_2 j PreH14 PreH18)
    as Hdirect.
  assert (Hwriter :
      WriterCounts ins locks_2 (j + 1) 0 k_pre
        (repeat_Z 0 (k_pre + 1))).
  { unfold WriterCounts. rewrite Hbefore.
    split.
    - unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
    - intros cell Hcell.
      unfold repeat_Z. rewrite Znth_repeat.
      split.
      + symmetry. apply set_card_empty__scan_entry.
        intros i [Hi _]. lia.
      + lia. }
  Exists (repeat_Z (-1) (k_pre + 1 - 1))
         (repeat_Z 0 (k_pre + 1)) locks_2 dead_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (xrows_cell_bounds__scan_entry k_pre m_pre n_pre xrows ins i j
       __default__List_Z PreH7 PreH9 PreH11 PreH12 PreH13
       (fun r Hr => proj2 (PreH15 r Hr)) ltac:(lia) ltac:(lia)) as Hcell.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (xrows_cell_bounds__scan_entry k_pre m_pre n_pre xrows ins i j
       __default__List_Z PreH7 PreH9 PreH11 PreH12 PreH13
       (fun r Hr => proj2 (PreH15 r Hr)) ltac:(lia) ltac:(lia)) as Hcell.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH15. lia. }
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins (@nil Z)) 0).
  { rewrite Hrow. eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hold : Znth i (lock_times_before locks_2 (j + 1)) 0 = 0).
  { pose proof PreH24 as Hscan.
    unfold DirectLockScan in Hscan.
    destruct Hscan as [_ [_ Hscan]].
    specialize (Hscan i ltac:(rewrite <- PreH15; lia)) as [_ Hsame].
    specialize (Hsame ltac:(lia)). lia. }
  assert (Hlive : ~ CellWasDead ins (lock_times_before locks_2 (j + 1))
      (j + 1 - 1) (Znth j (Znth i xrows __default__List_Z) 0)).
  { eapply dead_cell_false__direct_scan_step; [exact PreH23 | lia | exact PreH26]. }
  assert (Hcounts : WriterCounts ins locks_2 (j + 1) (i + 1) k_pre
      (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
        (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
        counts_2)).
  { eapply writer_counts_step__direct_scan_step; try eassumption; try lia.
    replace (j + 1 - 1) with j by lia. symmetry. exact Hcell. }
  assert (Hscan : DirectLockScan ins locks_2 (j + 1) (i + 1)).
  { eapply direct_lock_scan_step__direct_scan_step;
      [rewrite <- PreH15; lia | | exact PreH24].
    intros [_ [_ Hdead]]. apply Hlive.
    replace (j + 1 - 1) with j in Hdead |- * by lia.
    rewrite <- Hcell in Hdead. exact Hdead. }
  replace (Znth j (Znth i xrows __default__List_Z) 0 - 0)
    with (Znth j (Znth i xrows __default__List_Z) 0) in * by lia.
  Exists (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0 - 1)
      i firsts_2)
    (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
      (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
      counts_2)
    locks_2 dead_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg (&( "writers" )) (k_pre + 1)
      (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
        (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
        counts_2)).
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH15. lia. }
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins (@nil Z)) 0).
  { rewrite Hrow. eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hold : Znth i (lock_times_before locks_2 (j + 1)) 0 = 0).
  { pose proof PreH24 as Hscan.
    unfold DirectLockScan in Hscan.
    destruct Hscan as [_ [_ Hscan]].
    specialize (Hscan i ltac:(rewrite <- PreH15; lia)) as [_ Hsame].
    specialize (Hsame ltac:(lia)). lia. }
  assert (Hlive : ~ CellWasDead ins (lock_times_before locks_2 (j + 1))
      (j + 1 - 1) (Znth j (Znth i xrows __default__List_Z) 0)).
  { eapply dead_cell_false__direct_scan_step; [exact PreH23 | lia | exact PreH26]. }
  assert (Hcounts : WriterCounts ins locks_2 (j + 1) (i + 1) k_pre
      (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
        (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
        counts_2)).
  { eapply writer_counts_step__direct_scan_step; try eassumption; try lia.
    replace (j + 1 - 1) with j by lia. symmetry. exact Hcell. }
  assert (Hscan : DirectLockScan ins locks_2 (j + 1) (i + 1)).
  { eapply direct_lock_scan_step__direct_scan_step;
      [rewrite <- PreH15; lia | | exact PreH24].
    intros [_ [_ Hdead]]. apply Hlive.
    replace (j + 1 - 1) with j in Hdead |- * by lia.
    rewrite <- Hcell in Hdead. exact Hdead. }
  replace (Znth j (Znth i xrows __default__List_Z) 0 - 0)
    with (Znth j (Znth i xrows __default__List_Z) 0) in * by lia.
  Exists firsts_2
    (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
      (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
      counts_2)
    locks_2 dead_2.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg (&( "writers" )) (k_pre + 1)
      (replace_Znth (Znth j (Znth i xrows __default__List_Z) 0)
        (Znth (Znth j (Znth i xrows __default__List_Z) 0) counts_2 0 + 1)
        counts_2)).
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply writer_counts_skip_step__direct_scan_step; [lia | | exact PreH21].
  intros [Hold _].
  unfold DirectLockScan in PreH20.
  destruct PreH20 as [_ [_ Hscan]].
  specialize (Hscan i ltac:(lia)) as [Hiff Hsame].
  assert (Hnot_t : Znth i locks_2 0 <> j + 1).
  { intro Heq. apply Hiff in Heq. lia. }
  specialize (Hsame Hnot_t). lia.
Qed.

Lemma proof_of_solver_entail_wit_10_3_split_goal_2 : solver_entail_wit_10_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply direct_lock_scan_step__direct_scan_step; [lia | | exact PreH20].
  intros [Hold _].
  unfold DirectLockScan in PreH20.
  destruct PreH20 as [_ [_ Hscan]].
  specialize (Hscan i ltac:(lia)) as [Hiff Hsame].
  assert (Hnot_t : Znth i locks_2 0 <> j + 1).
  { intro Heq. apply Hiff in Heq. lia. }
  specialize (Hsame Hnot_t). lia.
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins __default__List_Z) 0).
  { eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH12. lia. }
  eapply writer_counts_skip_step__direct_scan_step; [lia | | exact PreH22].
  intros [_ [Hnz _]].
  replace (j + 1 - 1) with j in Hnz by lia.
  rewrite Hrow in Hnz.
  rewrite <- Hcell, PreH1 in Hnz. contradiction.
Qed.

Lemma proof_of_solver_entail_wit_10_4_split_goal_2 : solver_entail_wit_10_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins __default__List_Z) 0).
  { eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH12. lia. }
  eapply direct_lock_scan_step__direct_scan_step; [lia | | exact PreH21].
  intros [_ [Hnz _]].
  replace (j + 1 - 1) with j in Hnz by lia.
  rewrite Hrow in Hnz.
  rewrite <- Hcell, PreH1 in Hnz. contradiction.
Qed.

Lemma proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_10_5_split_goal_1 : solver_entail_wit_10_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins __default__List_Z) 0).
  { eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH14. lia. }
  assert (Hcell_nil : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins (@nil Z)) 0) by (rewrite Hrow; exact Hcell).
  assert (Hwas : CellWasDead ins (lock_times_before locks_2 (j + 1)) (j + 1 - 1)
      (Znth (j + 1 - 1) (Znth i ins (@nil Z)) 0)).
  { eapply dead_cell_true__direct_scan_step; [exact PreH22 | |].
    - replace (j + 1 - 1) with j by lia. rewrite <- Hcell_nil. lia.
    - replace (Znth (j + 1 - 1) (Znth i ins (@nil Z)) 0)
        with (Znth j (Znth i xrows __default__List_Z) 0) by
          (replace (j + 1 - 1) with j by lia; exact Hcell_nil).
      exact PreH25. }
  assert (Hnext : WriterCounts ins locks_2 (j + 1) (i + 1) k_pre counts_2).
  { eapply writer_counts_skip_step__direct_scan_step; [lia | | exact PreH24].
    intros [_ [_ Hnot]]. apply Hnot. exact Hwas. }
  assert (Hlockslen : Zlength locks_2 = Zlength ins).
  { unfold DirectLockScan in PreH23. tauto. }
  unfold WriterCounts in Hnext |- *.
  rewrite (lock_times_before_update__direct_scan_step locks_2 i (j + 1)
    ltac:(rewrite Hlockslen, <- PreH14; lia) PreH4).
  exact Hnext.
Qed.

Lemma proof_of_solver_entail_wit_10_5_split_goal_2 : solver_entail_wit_10_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcell : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins __default__List_Z) 0).
  { eapply xrow_cell__direct_scan_step; eauto; lia. }
  assert (Hrow : Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { apply Znth_indep. rewrite <- PreH14. lia. }
  assert (Hcell_nil : Znth j (Znth i xrows __default__List_Z) 0 =
      Znth j (Znth i ins (@nil Z)) 0) by (rewrite Hrow; exact Hcell).
  assert (Hwas : CellWasDead ins (lock_times_before locks_2 (j + 1)) (j + 1 - 1)
      (Znth (j + 1 - 1) (Znth i ins (@nil Z)) 0)).
  { eapply dead_cell_true__direct_scan_step; [exact PreH22 | |].
    - replace (j + 1 - 1) with j by lia. rewrite <- Hcell_nil. lia.
    - replace (j + 1 - 1) with j. 2:lia.
      rewrite <- Hcell_nil. exact PreH25. }
  assert (Hlockslen : Zlength locks_2 = Zlength ins).
  { unfold DirectLockScan in PreH23. tauto. }
  eapply direct_lock_scan_lock_step__direct_scan_step.
  - lia.
  - exact Hlockslen.
  - exact PreH4.
  - replace (j + 1 - 1) with j by lia. rewrite <- Hcell_nil. exact PreH3.
  - exact Hwas.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_10_5_split_goal_3 : solver_entail_wit_10_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlockslen : Zlength locks_2 = Zlength ins).
  { unfold DirectLockScan in PreH23. tauto. }
  eapply dead_cells_before_lock_update__direct_scan_step.
  - rewrite Hlockslen, <- PreH14. lia.
  - exact PreH4.
  - exact PreH22.
Qed.

Lemma proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_5_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength ins) by lia.
  pose proof (direct_scan_complete__collision_init_mark
    ins locks_2 counts_2 dead_2 (j + 1) i k_pre
    PreH2 Hi PreH19 PreH20 PreH18) as [_ [_ Hclosure]].
  exact Hclosure.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength ins) by lia.
  pose proof (direct_scan_complete__collision_init_mark
    ins locks_2 counts_2 dead_2 (j + 1) i k_pre
    PreH2 Hi PreH19 PreH20 PreH18) as [_ [Hmarks _]].
  exact Hmarks.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_3 : solver_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with n_pre in PreH20 by lia.
  exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_4 : solver_entail_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH13; assumption.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_5 : solver_entail_wit_11_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_6 : solver_entail_wit_11_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9; assumption.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (c - 0) with c in PreH1 by lia.
  eapply cell_marks_set_collision__collision_init_mark.
  - lia.
  - exact PreH4.
  - apply Z.ge_le. exact PreH1.
  - exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (c - 0) with c in PreH1 by lia.
  apply Z.ge_le. exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH14; assumption.
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_12_split_goal_5 : solver_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10; assumption.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_12_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow := PreH15 i ltac:(lia)).
  destruct Hrow as [_ Hsub].
  assert (Hrow_default :
            Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { unfold Znth. apply nth_indep.
    pose proof PreH12 as Hlenins.
    rewrite Zlength_correct in Hlenins. lia. }
  assert (Hcell : Znth (j + 1 - 1) (Znth i ins (@nil Z)) 0 = c).
  { replace (j + 1 - 1) with j by lia.
    rewrite Hrow_default.
    rewrite <- Hsub.
    rewrite Znth_sublist0 by lia.
    exact PreH1. }
  eapply collision_closure_step_match__collision_core_closure;
    try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_2 : solver_entail_wit_13_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength locks_2 = Zlength ins).
  { unfold CollisionClosurePrefix in PreH25. tauto. }
  eapply cell_marks_current_lock_stable__collision_core_closure;
    try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_3 : solver_entail_wit_13_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength locks_2 = Zlength ins).
  { unfold CollisionClosurePrefix in PreH25. tauto. }
  eapply writer_counts_current_lock_stable__collision_core_closure;
    try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply collision_closure_step_skip__collision_core_closure.
  - lia.
  - left. exact PreH1.
  - exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_3_split_goal_1 : solver_entail_wit_13_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow := PreH15 i ltac:(lia)).
  destruct Hrow as [_ Hsub].
  assert (Hrow_default :
            Znth i ins (@nil Z) = Znth i ins __default__List_Z).
  { unfold Znth. apply nth_indep.
    pose proof PreH12 as Hlenins.
    rewrite Zlength_correct in Hlenins. lia. }
  assert (Hcell : Znth (j + 1 - 1) (Znth i ins (@nil Z)) 0 <> c).
  { replace (j + 1 - 1) with j by lia.
    rewrite Hrow_default.
    rewrite <- Hsub.
    rewrite Znth_sublist0 by lia.
    exact PreH1. }
  eapply collision_closure_step_skip__collision_core_closure.
  - lia.
  - right. exact Hcell.
  - exact PreH25.
Qed.

Lemma proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_13_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  eapply collision_closure_cycle_dead__collision_cell_exit.
  - lia.
  - exact PreH1.
  - exact PreH17.
  - rewrite <- PreH10. exact PreH18.
  - exact PreH19.
  - exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  eapply collision_closure_cycle_complete__collision_cell_exit.
  - lia.
  - exact PreH1.
  - exact PreH17.
  - intros i Hi.
    assert (Hlen := PreH11 i ltac:(rewrite PreH10; exact Hi)).
    rewrite (Znth_indep ins i nil __default__List_Z) by exact Hi.
    lia.
  - intros i Hi.
    replace (j + 1 - 1) with j by lia.
    rewrite <- (Znth_concat_uniform__collision_cell_exit
      ins m_pre nil i j Hi).
    + apply PreH9. rewrite PreH10. nia.
    + intros r Hr.
      rewrite (Znth_indep ins r nil __default__List_Z) by exact Hr.
      apply PreH11. rewrite PreH10. exact Hr.
    + lia.
  - rewrite <- PreH10. exact PreH18.
  - exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_3 : solver_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_4 : solver_entail_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_5 : solver_entail_wit_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_spatial : solver_entail_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply IntArray.seg_to_undef_seg.
  sep_apply IntArray.seg_to_undef_seg.
  sep_apply (IntArray.undef_seg_merge_to_undef_seg (&("writers")) 0 (k_pre + 1) 105); try lia.
  sep_apply (IntArray.undef_seg_merge_to_undef_seg (&("first")) 0 1 (k_pre + 1)); try lia.
  sep_apply (IntArray.undef_seg_merge_to_undef_seg (&("first")) 0 (k_pre + 1) 105); try lia.
  sep_apply IntArray.undef_seg_to_undef_full; try lia.
  sep_apply IntArray.undef_seg_to_undef_full; try lia.
  cancel.
  sep_apply (IntArray.undef_seg_to_undef_full (&("writers")) 0 105); try lia.
  simpl.
  replace (&("writers") + 0) with (&("writers")) by lia.
  replace (&("first") + 0 + 0) with (&("first")) by lia.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_spatial.
  - sep_apply (proof_of_solver_entail_wit_14_split_goal_1
        k_pre m_pre n_pre xrows ins firsts dead_2 locks_2 counts c j
        __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20); cancel.
  - sep_apply (proof_of_solver_entail_wit_14_split_goal_2
        k_pre m_pre n_pre xrows ins firsts dead_2 locks_2 counts c j
        __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20); cancel.
  - sep_apply (proof_of_solver_entail_wit_14_split_goal_3
        k_pre m_pre n_pre xrows ins firsts dead_2 locks_2 counts c j
        __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20); cancel.
  - sep_apply (proof_of_solver_entail_wit_14_split_goal_4
        k_pre m_pre n_pre xrows ins firsts dead_2 locks_2 counts c j
        __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20); cancel.
  - sep_apply (proof_of_solver_entail_wit_14_split_goal_5
        k_pre m_pre n_pre xrows ins firsts dead_2 locks_2 counts c j
        __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20); cancel.
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_1 : solver_entail_wit_15_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply collision_closure_cell_complete__collision_cell_exit.
  - exact PreH1.
  - exact PreH20.
  - exact PreH10.
  - exact PreH23.
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_2 : solver_entail_wit_15_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH13; exact H.
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_3 : solver_entail_wit_15_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_15_1_split_goal_4 : solver_entail_wit_15_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9; exact H.
Qed.

Lemma proof_of_solver_entail_wit_15_1 : solver_entail_wit_15_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_15_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_15_2_split_goal_1 : solver_entail_wit_15_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply collision_closure_advance_no_collision__collision_cell_exit.
  - replace c with (c - 0) by lia; exact PreH1.
  - exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_15_2_split_goal_2 : solver_entail_wit_15_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply cell_marks_prefix_advance_no_collision__collision_cell_exit.
  - lia.
  - replace c with (c - 0) by lia; exact PreH1.
  - exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_15_2 : solver_entail_wit_15_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_15_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_15_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LockTimesThrough in PreH16.
  destruct PreH16 as [Hlength _].
  lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply lock_times_through_complete_spec__final_return with (m := m_pre).
  - intros i Hi.
    rewrite (Znth_indep ins i (@nil Z) __default__List_Z) by lia.
    apply PreH11.
    lia.
  - replace m_pre with j by lia.
    exact PreH16.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_2.
Qed.
