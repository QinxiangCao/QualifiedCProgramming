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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P038_1365C_rotation_matching_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P038_1365C_rotation_matching_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P038_1365C_rotation_matching_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold PositionTable in PreH9, PreH10.
  destruct PreH9 as [_ [_ [_ Hpa]]].
  destruct PreH10 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold PositionTable in PreH9, PreH10.
  destruct PreH9 as [_ [_ [_ Hpa]]].
  destruct PreH10 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix in PreH13.
  destruct PreH13 as [_ [_ Hall]].
  specialize (Hall shift ltac:(lia)) as [_ Hbound].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix in PreH13.
  destruct PreH13 as [_ [_ Hall]].
  specialize (Hall shift ltac:(lia)) as [_ Hbound].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace n_pre with (n_pre - 1 + 1) at 1 by lia.
  rewrite (IntArray.undef_full_unfold cnt_pre (n_pre - 1) (@nil Z)) by lia.
  replace (cnt_pre + 0 * sizeof(INT)) with cnt_pre by lia.
  sep_apply_l_atomic (valid_undef_store_int cnt_pre).
  Intros_p Hvalid.
  dump_pre_spatial.
  unfold isvalidptr_int in Hvalid.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
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
  assert (Harray : forall p (k : nat),
    IntArray.undef_full p (Z.of_nat k) |--
    UCharArray.undef_full p (4 * Z.of_nat k)).
  {
    intros p k. revert p.
    induction k as [|k IH]; intros p.
    - simpl. rewrite IntArray.undef_full_empty.
      rewrite UCharArray.undef_full_empty. cancel.
    - rewrite Nat2Z.inj_succ.
      rewrite (IntArray.undef_full_unfold p (Z.of_nat k) (@nil Z)) by lia.
      sep_apply_l_atomic
        (IntArray.undef_seg_to_undef_full p 1 (Z.succ (Z.of_nat k))).
      replace (p + 0 * sizeof(INT)) with p by lia.
      sep_apply_l_atomic (Hcell p).
      try rewrite sizeof_int in *.
      try rewrite sizeof_uchar in *.
      replace (p + 1 * 4) with (p + 4) by lia.
      replace (Z.succ (Z.of_nat k) - 1) with (Z.of_nat k) by lia.
      sep_apply_l_atomic (IH (p + 4)).
      replace (4 * Z.succ (Z.of_nat k)) with (4 + 4 * Z.of_nat k) by lia.
      sep_apply_r_atomic
        (UCharArray.undef_full_merge_to_undef_full
          p 4 (4 + 4 * Z.of_nat k)).
      + dump_pre_spatial. pose proof (Nat2Z.is_nonneg k). lia.
      + replace (p + 4 * 1) with (p + 4) by lia.
        replace (4 + 4 * Z.of_nat k - 4) with (4 * Z.of_nat k) by lia.
        cancel.
      rewrite sizeof_uchar.
      replace (p + 4 * 1) with (p + 4) by lia.
      cancel.
  }
  replace n_pre with (Z.of_nat (Z.to_nat n_pre)) by lia.
  sep_apply_l_atomic (Harray cnt_pre (Z.to_nat n_pre)).
  rewrite sizeof_int.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Pre in PreH2.
  destruct PreH2 as [Ha Hb].
  eapply position_table_from_permutation_inverse__setup_layout.
  - exact PreH8.
  - exact PreH11.
  - rewrite PreH8 in Hb. exact Hb.
  - exact PreH6.
  - intros i Hi. apply (proj2 (PreH12 i Hi)).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold Pre in PreH2.
  destruct PreH2 as [Ha Hb].
  eapply position_table_from_permutation_inverse__setup_layout.
  - symmetry. exact PreH7.
  - exact PreH10.
  - rewrite <- PreH7 in Ha. exact Ha.
  - exact PreH5.
  - intros i Hi. apply (proj1 (PreH12 i Hi)).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
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
  assert (Harray : forall (k : nat) p,
    aligned_4 p ->
    UCharArray.full p (4 * Z.of_nat k) (repeat 0 (4 * k)%nat) |--
    IntArray.full p (Z.of_nat k) (repeat 0 k)).
  {
    induction k as [|k IH]; intros p Halign.
    - unfold UCharArray.full, IntArray.full, store_array.
      cbn. Intros_p Hzero. Intros_p Hnil.
      split_pure_spatial.
      + cancel emp.
      + split_pures; dump_pre_spatial; auto.
    - replace (repeat 0 (4 * S k)%nat)
        with (repeat 0 4%nat ++ repeat 0 (4 * k)%nat).
      2:{ rewrite <- repeat_app. f_equal. lia. }
      replace (repeat 0 (S k)) with (0 :: repeat 0 k) by reflexivity.
      sep_apply_l_atomic
        (UCharArray.full_to_seg p (4 * Z.of_nat (S k))
          (repeat 0 4%nat ++ repeat 0 (4 * k)%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_split_to_seg p 0 4 (4 * Z.of_nat (S k))
          (repeat 0 4%nat ++ repeat 0 (4 * k)%nat) ltac:(lia)).
      replace (4 - 0) with (Zlength (repeat 0 4%nat)) by
        (rewrite Zlength_correct, repeat_length; lia).
      rewrite sublist_app_exact1.
      rewrite (sublist_split_app_r (Zlength (repeat 0 4%nat))
        (4 * Z.of_nat (S k) - 0) 4
        (repeat 0 4%nat) (repeat 0 (4 * k)%nat)) by
          (rewrite Zlength_correct, repeat_length; lia).
      replace (4 * Z.of_nat (S k) - 4) with (4 * Z.of_nat k) by lia.
      rewrite sublist_self by
        (rewrite Zlength_correct, repeat_length; lia).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 0 4 (repeat 0 4%nat)).
      sep_apply_l_atomic
        (UCharArray.seg_to_full p 4 (4 * Z.of_nat (S k))
          (repeat 0 (4 * k)%nat)).
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
      replace (4 * Z.of_nat (S k) - 4) with (4 * Z.of_nat k) by lia.
      sep_apply_l_atomic (IH (p + 4) Halign4).
      pose proof
        (IntArray.full_merge_to_full p 1 (Z.of_nat (S k))
          (repeat 0 1%nat) (repeat 0 k) ltac:(lia)) as Hmerge.
      replace (p + 1 * sizeof(INT)) with (p + 4) in Hmerge by
        (rewrite sizeof_int; lia).
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) in Hmerge by lia.
      sep_apply Hmerge.
      cbn. reflexivity.
  }
  pose proof (Harray (Z.to_nat n_pre) cnt_pre PreH9) as Hwhole.
  replace (Z.of_nat (Z.to_nat n_pre)) with n_pre in Hwhole by lia.
  unfold repeat_Z.
  rewrite sizeof_int.
  replace (Z.to_nat (4 * n_pre)) with (4 * Z.to_nat n_pre)%nat by lia.
  exact Hwhole.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix.
  split.
  - unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  - split; [lia |].
    intros s Hs.
    unfold repeat_Z. rewrite Znth_repeat.
    split.
    + symmetry. apply set_card_empty__setup_layout.
      intros v [Hv _]. lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PositionTable in PreH10, PreH11.
  destruct PreH10 as [_ [_ [_ Hpa]]].
  destruct PreH11 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  symmetry.
  apply Z.rem_small.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PositionTable in PreH10, PreH11.
  destruct PreH10 as [_ [_ [_ Hpa]]].
  destruct PreH11 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  lia.
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
  unfold PositionTable in PreH10, PreH11.
  destruct PreH10 as [_ [_ [_ Hpa]]].
  destruct PreH11 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  replace (Znth v pa_spec 0 - Znth v pb_spec 0 + n_pre)
    with ((Znth v pa_spec 0 - Znth v pb_spec 0) + 1 * n_pre) by ring.
  rewrite Z.rem_add by nia.
  symmetry.
  apply Z.rem_small.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PositionTable in PreH10, PreH11.
  destruct PreH10 as [_ [_ [_ Hpa]]].
  destruct PreH11 as [_ [_ [_ Hpb]]].
  specialize (Hpa v ltac:(lia)).
  specialize (Hpb v ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply rotation_tally_prefix_step__tally_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix in PreH11.
  destruct PreH11 as [Hlen _].
  unfold CountPrefixMaximum.
  split; [lia |].
  split; [lia |].
  split.
  - intros i Hi. lia.
  - split; intros; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = n_pre + 1) by lia.
  subst v.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix in PreH12.
  destruct PreH12 as [Hlen _].
  eapply count_prefix_max_step_gt__tally_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RotationTallyPrefix in PreH12.
  destruct PreH12 as [Hlen [_ Hall]].
  specialize (Hall s ltac:(lia)) as [_ Hnonneg].
  eapply count_prefix_max_step_le__tally_transitions; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold PositionTable in PreH9, PreH10.
  destruct PreH9 as [_ [_ [Ha _]]].
  destruct PreH10 as [_ [_ [Hb _]]].
  intros i Hi.
  split.
  - exact (proj2 (Ha i Hi)).
  - exact (proj2 (Hb i Hi)).
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_2 : solver_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold PositionTable in PreH10.
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_3 : solver_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold PositionTable in PreH9.
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_4 : solver_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (s = n_pre) by lia.
  subst s.
  apply (rotation_tally_max_implies_spec__final_result
    a b pa_spec_2 pb_spec_2 n_pre counts best);
    assumption || lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_to_full_shape cnt_pre n_pre counts).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_4.
Qed.
