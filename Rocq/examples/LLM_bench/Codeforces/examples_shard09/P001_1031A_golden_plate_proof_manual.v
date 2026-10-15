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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P001_1031A_golden_plate_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P001_1031A_golden_plate_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P001_1031A_golden_plate_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = k_pre) by lia.
  subst i.
  subst total.
  unfold Spec.
  assert (Hwk : 4 * k_pre <= w_pre + 1).
  { pose proof (Z.le_min_l w_pre h_pre). lia. }
  assert (Hhk : 4 * k_pre <= h_pre + 1).
  { pose proof (Z.le_min_r w_pre h_pre). lia. }
  set (layer := fun j : Z =>
    map (fun c => (2 * j, c)) (SumLib.ZRange.Zrange (2 * j) (h_pre - 2 * j)) ++
    map (fun c => (w_pre - 1 - 2 * j, c)) (SumLib.ZRange.Zrange (2 * j) (h_pre - 2 * j)) ++
    map (fun r => (r, 2 * j)) (SumLib.ZRange.Zrange (2 * j + 1) (w_pre - 1 - 2 * j)) ++
    map (fun r => (r, h_pre - 1 - 2 * j))
      (SumLib.ZRange.Zrange (2 * j + 1) (w_pre - 1 - 2 * j))).
  assert (Hlayer_bounds : forall j, 0 <= j < k_pre ->
      4 * j <= w_pre - 3 /\ 4 * j <= h_pre - 3).
  { intros j Hj. split; lia. }
  assert (Hlayer_mem : forall j r c, 0 <= j < k_pre ->
      In (r, c) (layer j) <->
      0 <= r < w_pre /\ 0 <= c < h_pre /\
      (((r = 2 * j \/ r = w_pre - 1 - 2 * j) /\
          2 * j <= c < h_pre - 2 * j) \/
       ((c = 2 * j \/ c = h_pre - 1 - 2 * j) /\
          2 * j <= r < w_pre - 2 * j))).
  {
    intros j r c Hj.
    pose proof (Hlayer_bounds j Hj) as [Hjw Hjh].
    unfold layer.
    rewrite !in_app_iff.
    repeat rewrite in_map_iff.
    repeat rewrite <- SumLib.ZRange.In_Zrange.
    split.
    - intros [[x [E Hx]] | [[x [E Hx]] | [[x [E Hx]] | [x [E Hx]]]]];
        inversion E; subst; clear E.
      + rewrite <- SumLib.ZRange.In_Zrange in Hx.
        split.
        * change (0 <= 2 * j < w_pre). lia.
        * split; [lia |].
          left. split; [left; reflexivity | lia].
      + rewrite <- SumLib.ZRange.In_Zrange in Hx.
        split.
        * change (0 <= w_pre - 1 - 2 * j < w_pre). lia.
        * split; [lia |]. left. split; [right; reflexivity | lia].
      + rewrite <- SumLib.ZRange.In_Zrange in Hx.
        split; [lia |].
        split.
        * change (0 <= 2 * j < h_pre). lia.
        * right. split; [left; reflexivity | lia].
      + rewrite <- SumLib.ZRange.In_Zrange in Hx.
        split; [lia |].
        split.
        * change (0 <= h_pre - 1 - 2 * j < h_pre). lia.
        * right. split; [right; reflexivity | lia].
    - intros [Hr [Hc [Hhor | Hvert]]].
      + destruct Hhor as [[Er | Er] Hcr]; subst r.
        * left. exists c. split; [reflexivity |].
          rewrite <- SumLib.ZRange.In_Zrange. exact Hcr.
        * right; left. exists c. split; [reflexivity |].
          rewrite <- SumLib.ZRange.In_Zrange. exact Hcr.
      + destruct Hvert as [[Ec | Ec] Hrr]; subst c.
        * destruct (Z.eq_dec r (2 * j)) as [Er | Er].
          -- subst r. left. exists (2 * j). split; [reflexivity |].
             rewrite <- SumLib.ZRange.In_Zrange. lia.
          -- destruct (Z.eq_dec r (w_pre - 1 - 2 * j)) as [Er' | Er'].
             ++ subst r. right; left. exists (2 * j). split; [reflexivity |].
                rewrite <- SumLib.ZRange.In_Zrange. lia.
             ++ right; right; left. exists r. split; [reflexivity |].
                rewrite <- SumLib.ZRange.In_Zrange. lia.
        * destruct (Z.eq_dec r (2 * j)) as [Er | Er].
          -- subst r. left. exists (h_pre - 1 - 2 * j).
             split; [reflexivity |]. rewrite <- SumLib.ZRange.In_Zrange. lia.
          -- destruct (Z.eq_dec r (w_pre - 1 - 2 * j)) as [Er' | Er'].
             ++ subst r. right; left. exists (h_pre - 1 - 2 * j).
                split; [reflexivity |]. rewrite <- SumLib.ZRange.In_Zrange. lia.
             ++ right; right; right. exists r. split; [reflexivity |].
                rewrite <- SumLib.ZRange.In_Zrange. lia.
  }
  assert (Hlayer_nodup : forall j, 0 <= j < k_pre -> NoDup (layer j)).
  {
    intros j Hj.
    pose proof (Hlayer_bounds j Hj) as [Hjw Hjh].
    unfold layer.
    apply NoDup_app.
    - apply FinFun.Injective_map_NoDup.
      + intros x y E. inversion E. reflexivity.
      + apply SumLib.ZRange.NoDup_Zrange.
    - apply NoDup_app.
      + apply FinFun.Injective_map_NoDup.
        * intros x y E. inversion E. reflexivity.
        * apply SumLib.ZRange.NoDup_Zrange.
      + apply NoDup_app.
        * apply FinFun.Injective_map_NoDup.
          -- intros x y E. inversion E. reflexivity.
          -- apply SumLib.ZRange.NoDup_Zrange.
        * apply FinFun.Injective_map_NoDup.
          -- intros x y E. inversion E. reflexivity.
          -- apply SumLib.ZRange.NoDup_Zrange.
        * intros [r c] HC HD.
          apply in_map_iff in HC as [x [EC HC]].
          apply in_map_iff in HD as [y [ED HD]].
          rewrite <- SumLib.ZRange.In_Zrange in HC, HD.
          pose proof (f_equal (@snd Z Z) EC) as E1.
          pose proof (f_equal (@snd Z Z) ED) as E2.
          simpl in E1, E2.
          change (2 * j = c) in E1.
          change (h_pre - 1 - 2 * j = c) in E2. lia.
      + intros [r c] HB HCD.
        apply in_map_iff in HB as [x [EB HB]].
        rewrite <- SumLib.ZRange.In_Zrange in HB.
        rewrite in_app_iff in HCD.
        destruct HCD as [HC | HD]; apply in_map_iff in HC || apply in_map_iff in HD.
        * destruct HC as [y [EC HC]]. rewrite <- SumLib.ZRange.In_Zrange in HC.
          pose proof (f_equal (@fst Z Z) EB) as E1.
          pose proof (f_equal (@fst Z Z) EC) as E2.
          simpl in E1, E2.
          change (w_pre - 1 - 2 * j = r) in E1.
          change (y = r) in E2. lia.
        * destruct HD as [y [ED HD]]. rewrite <- SumLib.ZRange.In_Zrange in HD.
          pose proof (f_equal (@fst Z Z) EB) as E1.
          pose proof (f_equal (@fst Z Z) ED) as E2.
          simpl in E1, E2.
          change (w_pre - 1 - 2 * j = r) in E1.
          change (y = r) in E2. lia.
    - intros [r c] HA HBCD.
      apply in_map_iff in HA as [x [EA HA]].
      rewrite <- SumLib.ZRange.In_Zrange in HA.
      rewrite !in_app_iff in HBCD.
      destruct HBCD as [HB | [HC | HD]].
      + apply in_map_iff in HB as [y [EB HB]]. rewrite <- SumLib.ZRange.In_Zrange in HB.
        pose proof (f_equal (@fst Z Z) EA) as E1.
        pose proof (f_equal (@fst Z Z) EB) as E2.
        simpl in E1, E2.
        change (2 * j = r) in E1.
        change (w_pre - 1 - 2 * j = r) in E2. lia.
      + apply in_map_iff in HC as [y [EC HC]]. rewrite <- SumLib.ZRange.In_Zrange in HC.
        pose proof (f_equal (@fst Z Z) EA) as E1.
        pose proof (f_equal (@fst Z Z) EC) as E2.
        simpl in E1, E2.
        change (2 * j = r) in E1.
        change (y = r) in E2. lia.
      + apply in_map_iff in HD as [y [ED HD]]. rewrite <- SumLib.ZRange.In_Zrange in HD.
        pose proof (f_equal (@fst Z Z) EA) as E1.
        pose proof (f_equal (@fst Z Z) ED) as E2.
        simpl in E1, E2.
        change (2 * j = r) in E1.
        change (y = r) in E2. lia.
  }
  assert (Hunique_layer : forall j l r c,
      0 <= j < k_pre -> 0 <= l < k_pre ->
      In (r, c) (layer j) -> In (r, c) (layer l) -> j = l).
  {
    intros j l r c Hj Hl Hjm Hlm.
    apply Hlayer_mem in Hjm; [|exact Hj].
    apply Hlayer_mem in Hlm; [|exact Hl].
    destruct Hjm as [_ [_ [Hjhor | Hjvert]]];
    destruct Hlm as [_ [_ [Hlhor | Hlvert]]].
    - destruct Hjhor as [[E1 | E1] R1];
      destruct Hlhor as [[E2 | E2] R2]; lia.
    - destruct Hjhor as [[E1 | E1] R1];
      destruct Hlvert as [[E2 | E2] R2]; lia.
    - destruct Hjvert as [[E1 | E1] R1];
      destruct Hlhor as [[E2 | E2] R2]; lia.
    - destruct Hjvert as [[E1 | E1] R1];
      destruct Hlvert as [[E2 | E2] R2]; lia.
  }
  set (pairs := flat_map layer (SumLib.ZRange.Zrange 0 k_pre)).
  assert (Hflat_nodup : forall xs : list Z,
      NoDup xs ->
      (forall j, In j xs -> 0 <= j < k_pre) ->
      NoDup (flat_map layer xs)).
  {
    intros xs Hnd.
    induction Hnd as [|a xs Hnot Hnd IH]; intros Hrange; simpl.
    - constructor.
    - apply NoDup_app.
      + apply Hlayer_nodup. apply Hrange. left. reflexivity.
      + apply IH. intros j Hj. apply Hrange. right. exact Hj.
      + intros [r c] Ha Htail.
        apply in_flat_map in Htail as [b [Hb Hbc]].
        assert (a = b).
        { eapply Hunique_layer.
          - apply Hrange. left. reflexivity.
          - apply Hrange. right. exact Hb.
          - exact Ha.
          - exact Hbc. }
        subst b. contradiction.
  }
  assert (Hpairs_nodup : NoDup pairs).
  {
    unfold pairs.
    apply Hflat_nodup.
    - apply SumLib.ZRange.NoDup_Zrange.
    - intros j Hj. rewrite <- SumLib.ZRange.In_Zrange in Hj. exact Hj.
  }
  assert (HZrange_length : forall lo hi, lo <= hi ->
      Z.of_nat (length (SumLib.ZRange.Zrange lo hi)) = hi - lo).
  {
    intros lo hi Hle.
    unfold SumLib.ZRange.Zrange.
    assert (Haux : forall n x, length (SumLib.ZRange.Zrange_aux x n) = n).
    { induction n; intros; simpl; [reflexivity | now rewrite IHn]. }
    rewrite Haux, Z2Nat.id by lia. reflexivity.
  }
  assert (Hlayer_count : forall j, 0 <= j < k_pre ->
      Z.of_nat (length (layer j)) =
      2 * (w_pre + h_pre) - 16 * j - 4).
  {
    intros j Hj.
    pose proof (Hlayer_bounds j Hj) as [Hjw Hjh].
    unfold layer.
    rewrite !length_app, !length_map.
    repeat rewrite Nat2Z.inj_add.
    repeat rewrite HZrange_length by lia.
    ring.
  }
  assert (Hpair_count_aux : forall n low,
      0 <= low -> low + Z.of_nat n <= k_pre ->
      Z.of_nat (length (flat_map layer (SumLib.ZRange.Zrange_aux low n))) =
      Z.of_nat n * (2 * (w_pre + h_pre) - 16 * low - 4) -
      8 * Z.of_nat n * (Z.of_nat n - 1)).
  {
    induction n as [|n IH]; intros low Hlow Hbound.
    - simpl. ring.
    - change
        (Z.of_nat
           (length
              (layer low ++
               flat_map layer (SumLib.ZRange.Zrange_aux (low + 1) n))) =
         Z.of_nat (S n) * (2 * (w_pre + h_pre) - 16 * low - 4) -
         8 * Z.of_nat (S n) * (Z.of_nat (S n) - 1)).
      rewrite length_app, Nat2Z.inj_add.
      rewrite Hlayer_count by lia.
      rewrite IH by lia.
      rewrite Nat2Z.inj_succ.
      ring.
  }
  assert (Hpairs_count : Z.of_nat (length pairs) =
      2 * k_pre * (w_pre + h_pre - 2) -
      8 * k_pre * (k_pre - 1)).
  {
    unfold pairs, SumLib.ZRange.Zrange.
    rewrite Hpair_count_aux by lia.
    rewrite Z2Nat.id by lia.
    ring.
  }
  set (encoded := map (fun p : Z * Z => fst p * h_pre + snd p) pairs).
  assert (Hencoded_nodup : NoDup encoded).
  {
    unfold encoded.
    apply SumLib.FiniteExtra.Injective_map_NoDup_in.
    - intros [r1 c1] [r2 c2] H1 H2 E; simpl in E.
      unfold pairs in H1, H2.
      apply in_flat_map in H1 as [j1 [Hj1 H1]].
      apply in_flat_map in H2 as [j2 [Hj2 H2]].
      rewrite <- SumLib.ZRange.In_Zrange in Hj1, Hj2.
      apply Hlayer_mem in H1; [|exact Hj1].
      apply Hlayer_mem in H2; [|exact Hj2].
      destruct H1 as [Hr1 [Hc1 _]].
      destruct H2 as [Hr2 [Hc2 _]].
      assert (r1 = r2) by nia.
      subst r2. assert (c1 = c2) by nia. subst c2. reflexivity.
    - exact Hpairs_nodup.
  }
  assert (Hencoded_mem : forall z,
      In z encoded <->
      0 <= z < w_pre * h_pre /\
      RingCell w_pre h_pre k_pre (z / h_pre) (z mod h_pre)).
  {
    intros z.
    unfold encoded.
    rewrite in_map_iff.
    split.
    - intros [[r c] [Ez Hrc]]; simpl in Ez; subst z.
      unfold pairs in Hrc.
      apply in_flat_map in Hrc as [j [Hj Hrc]].
      rewrite <- SumLib.ZRange.In_Zrange in Hj.
      apply Hlayer_mem in Hrc; [|exact Hj].
      destruct Hrc as [Hr [Hc Hside]].
      assert (Hdiv : (r * h_pre + c) / h_pre = r).
      { symmetry. apply Z.div_unique with (r := c); lia. }
      assert (Hmod : (r * h_pre + c) mod h_pre = c).
      { symmetry. apply Z.mod_unique with (q := r); lia. }
      split; [nia |].
      unfold RingCell. rewrite Hdiv, Hmod.
      split; [exact Hr |]. split; [exact Hc |].
      exists j. split; assumption.
    - intros [Hz Hring].
      unfold RingCell in Hring.
      destruct Hring as [Hr [Hc [j [Hj Hside]]]].
      exists (z / h_pre, z mod h_pre). simpl.
      split.
      + symmetry. rewrite Z.mul_comm. apply Z.div_mod. lia.
      + unfold pairs. apply in_flat_map.
        exists j. split.
        * rewrite <- SumLib.ZRange.In_Zrange. exact Hj.
        * apply Hlayer_mem; [exact Hj |].
          split; [exact Hr |]. split; assumption.
  }
  set (P := fun z : Z =>
    0 <= z < w_pre * h_pre /\
    RingCell w_pre h_pre k_pre (z / h_pre) (z mod h_pre)).
  pose (FP := SumLib.ZRange.finite_Z_range' 0 (w_pre * h_pre)
    (fun z : Z => RingCell w_pre h_pre k_pre (z / h_pre) (z mod h_pre))).
  assert (Hperm : Permutation (@SumLib.Sum.enum Z P FP) encoded).
  {
    apply NoDup_Permutation.
    - apply SumLib.Sum.enum_nodup.
    - exact Hencoded_nodup.
    - intros z. rewrite <- SumLib.Sum.enum_ok. unfold P.
      symmetry. apply Hencoded_mem.
  }
  assert (Hfold_ones : forall xs : list Z,
      fold_right (fun _ acc => 1 + acc) 0 xs = Z.of_nat (length xs)).
  {
    induction xs as [|a xs IH].
    - reflexivity.
    - change (1 + fold_right (fun _ acc : Z => 1 + acc) 0 xs =
        Z.of_nat (S (length xs))).
      rewrite IH, Nat2Z.inj_succ. lia.
  }
  change (2 * k_pre * (w_pre + h_pre - 2) -
      8 * k_pre * (k_pre - 1) = @SpecHelpers.set_card Z P FP).
  unfold SpecHelpers.set_card, SumLib.Sum.sum.
  rewrite Hfold_ones.
  rewrite (Permutation_length Hperm).
  unfold encoded. rewrite length_map.
  symmetry. exact Hpairs_count.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
