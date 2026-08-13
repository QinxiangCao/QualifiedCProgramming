Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition Power2 (j : Z) : Z := Z.pow 2 j.

(** Program-safety and data-representation predicates.  These predicates do
    not claim that any sparse-table cell contains the right answer. *)
Definition RMQSizeSafe (n K : Z) : Prop :=
  1 <= n /\
  n <= 100000 /\
  1 <= K /\
  K <= 30 /\
  n * K <= 1000000 /\
  n < Power2 K.

Definition RMQInputValues (l : list Z) (n : Z) : Prop :=
  Zlength l = n /\
  forall i, 0 <= i < n -> -2147483648 <= Znth i l 0 <= 2147483647.

Definition STTableShape (st_ls : list Z) (K n : Z) : Prop :=
  Zlength st_ls = n * K.

Definition STCellBounds (st_ls : list Z) (K i j : Z) : Prop :=
  0 < K /\
  0 <= i /\
  0 <= j /\ j < K /\
  0 <= i * K + j < Zlength st_ls.

Definition STZeroPrefixBounds (st_ls : list Z) (upto : Z) : Prop :=
  0 <= upto /\ upto <= Zlength st_ls.

Definition STBasePrefixBounds (n upto : Z) : Prop :=
  0 <= upto /\ upto <= n.

Definition STBuiltBeforeLevelBounds (K level : Z) : Prop :=
  0 <= level /\ level <= K.

Definition STLevelPrefixBounds (K n j upto : Z) : Prop :=
  0 <= j /\ j < K /\ 0 <= upto /\ upto <= n.

Definition RangeMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  0 <= lo /\
  lo < hi /\
  hi <= Zlength l /\
  max_value_of_subset Z.le
    (fun k => lo <= k /\ k < hi)
    (fun k => Znth k l 0)
    ans.

Definition STCellRangeMax
    (l st_ls : list Z) (K i j : Z) : Prop :=
  RangeMaxValue l i (i + Power2 j) (Znth (i * K + j) st_ls 0).

Definition STZeroPrefix (st_ls : list Z) (upto : Z) : Prop :=
  forall p, 0 <= p < upto -> Znth p st_ls 0 = 0.

Definition STBasePrefix
    (l st_ls : list Z) (K n upto : Z) : Prop :=
  forall i, 0 <= i < upto -> STCellRangeMax l st_ls K i 0.

Definition STBuiltBeforeLevel
    (l st_ls : list Z) (K n level : Z) : Prop :=
  forall i j,
    0 <= i /\ 0 <= j /\ j < level /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.

Definition STLevelPrefix
    (l st_ls : list Z) (K n j upto : Z) : Prop :=
  forall i,
    0 <= i /\ i < upto /\ i + Power2 j <= n ->
    STCellRangeMax l st_ls K i j.

Definition STBuilt (l st_ls : list Z) (K n : Z) : Prop :=
  STBuiltBeforeLevel l st_ls K n K.

Definition QueryIntervalBounds (n left right : Z) : Prop :=
  0 <= left /\ left <= right /\ right < n.

Definition QueryLogBounds (K n len k pow : Z) : Prop :=
  1 <= len /\
  len <= n /\
  1 <= K /\
  n < Power2 K /\
  0 <= k /\
  k < K /\
  1 <= pow.

(** Mathematical progress of the integer-logarithm loop, independent of the
    enclosing C bounds used to justify arithmetic and table access. *)
Definition QueryLogLoopState (len k pow : Z) : Prop :=
  0 <= k /\
  pow = Power2 k /\
  Power2 k <= len.

Definition QueryLogFinalState (len k pow : Z) : Prop :=
  QueryLogLoopState len k pow /\
  len < Power2 (k + 1).

(* Helper imports migrated from rmq__vc_proving_subagent_merged_proof_manual.v. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

(* Helper lemmas migrated from rmq__vc_proving_subagent_merged_proof_manual.v. *)

Lemma worker_Power2_nonneg : forall j, 0 <= Power2 j.
Proof.
  intros j.
  unfold Power2.
  apply Z.pow_nonneg.
  lia.
Qed.

Lemma worker_Power2_bound_lt_30 :
  forall j K, K <= 30 -> j < K -> Power2 j <= 536870912.
Proof.
  intros j K HK Hj.
  unfold Power2.
  replace 536870912 with (2 ^ 29) by (vm_compute; reflexivity).
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma worker_Power2_double_int_bound_30 :
  forall j K, K <= 30 -> j < K -> Power2 j * 2 <= 2147483647.
Proof.
  intros j K HK Hj.
  pose proof (worker_Power2_bound_lt_30 j K HK Hj).
  pose proof (worker_Power2_nonneg j).
  lia.
Qed.

Lemma worker_Power2_plus_n_int_bound_30 :
  forall j K n i,
    K <= 30 ->
    j < K ->
    n <= 100000 ->
    i <= n ->
    i + Power2 j <= 2147483647.
Proof.
  intros j K n i HK Hj Hn Hi.
  pose proof (worker_Power2_bound_lt_30 j K HK Hj).
  lia.
Qed.

Lemma STZeroPrefix_replace_zero_step:
  forall st_ls idx,
    STZeroPrefix st_ls idx ->
    idx < Zlength st_ls ->
    STZeroPrefix (replace_Znth idx 0 st_ls) (idx + 1).
Proof.
  intros st_ls idx Hprefix Hidx.
  unfold STZeroPrefix in *.
  intros p Hp.
  destruct (Z.eq_dec p idx) as [Heq | Hneq].
  - subst.
    rewrite Znth_replace_Znth_Same; lia.
  - rewrite Znth_replace_Znth_Diff; try lia.
    apply Hprefix; lia.
Qed.

Lemma worker_Power2_0_1 : Power2 0 = 1.
Proof.
  unfold Power2; simpl; lia.
Qed.

Lemma worker_STBasePrefix_write_base_step :
  forall (l st_ls : list Z) (K n i : Z),
    Zlength l = n ->
    Zlength st_ls = n * K ->
    0 < K ->
    0 <= i ->
    i < n ->
    0 <= i * K ->
    i * K < n * K ->
    STBasePrefix l st_ls K n i ->
    STBasePrefix l (replace_Znth (i * K) (Znth i l 0) st_ls) K n (i + 1).
Proof.
  intros l st_ls K n i Hl Hst HK Hi0 Hin Hidx0 Hidxn Hbase.
  unfold STBasePrefix in *.
  intros p Hp.
  destruct (Z.eq_dec p i) as [-> | Hne].
  - unfold STCellRangeMax.
    unfold RangeMaxValue.
    rewrite worker_Power2_0_1.
    replace (i * K + 0) with (i * K) by lia.
    rewrite Znth_replace_Znth_Same; try rewrite Hst; try lia; try nia.
    repeat split; try lia.
    apply (@MaxMin.max_1 Z Z.le Interface.Zle_TotalOrder Z i
             (fun k : Z => i <= k < i + 1) (fun k : Z => Znth k l 0)).
    intros k; split; intros Hk; lia.
  - assert (Hp_old : 0 <= p < i) by lia.
    specialize (Hbase p Hp_old).
    unfold STCellRangeMax in *.
    rewrite Znth_replace_Znth_Diff; try exact Hbase; try rewrite Hst; try lia; try nia.
Qed.

Lemma worker_STBasePrefix_complete_level1 :
  forall (l st_ls : list Z) (K n i : Z),
    i >= n ->
    i <= n ->
    STBasePrefix l st_ls K n i ->
    STBuiltBeforeLevel l st_ls K n 1.
Proof.
  intros l st_ls K n i Hge Hle Hbase.
  unfold STBasePrefix in Hbase.
  unfold STBuiltBeforeLevel.
  intros p j Hj.
  destruct Hj as (Hp0 & Hj0 & Hjlt & Hrange).
  assert (j = 0) by lia; subst j.
  rewrite worker_Power2_0_1 in Hrange.
  apply Hbase.
  lia.
Qed.

Lemma Power2_pos : forall k,
  0 <= k ->
  0 < Power2 k.
Proof.
  intros.
  unfold Power2.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma Power2_sub1_double : forall j,
  1 <= j ->
  Power2 j = Power2 (j - 1) + Power2 (j - 1).
Proof.
  intros.
  replace j with ((j - 1) + 1) by lia.
  unfold Power2.
  rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  replace (j - 1 + 1 - 1) with (j - 1) by lia.
  set (p := 2 ^ (j - 1)); lia.
Qed.

Lemma cell_index_mod : forall row K col,
  0 < K ->
  0 <= col < K ->
  (row * K + col) mod K = col.
Proof.
  intros.
  replace (row * K + col) with (col + row * K) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

Lemma cell_index_col_eq : forall row1 row2 K col1 col2,
  0 < K ->
  0 <= col1 < K ->
  0 <= col2 < K ->
  row1 * K + col1 = row2 * K + col2 ->
  col1 = col2.
Proof.
  intros.
  pose proof (f_equal (fun z => z mod K) H2) as Hmod.
  cbn in Hmod.
  rewrite !cell_index_mod in Hmod by auto.
  exact Hmod.
Qed.

Lemma cell_index_diff_col_neq : forall row1 row2 K col1 col2,
  0 < K ->
  0 <= col1 < K ->
  0 <= col2 < K ->
  col1 <> col2 ->
  row1 * K + col1 <> row2 * K + col2.
Proof.
  intros ? ? ? ? ? ? ? ? Hdiff Heq.
  apply Hdiff.
  eapply cell_index_col_eq; eauto.
Qed.

Lemma cell_index_same_col_eq : forall row1 row2 K col,
  0 < K ->
  row1 * K + col = row2 * K + col ->
  row1 = row2.
Proof.
  intros.
  assert (row1 * K = row2 * K) by lia.
  eapply Z.mul_reg_r; eauto; lia.
Qed.

Lemma cell_index_same_col_neq : forall row1 row2 K col,
  0 < K ->
  row1 <> row2 ->
  row1 * K + col <> row2 * K + col.
Proof.
  intros ? ? ? ? HK Hneq Heq.
  apply Hneq.
  eapply cell_index_same_col_eq; eauto.
Qed.

Lemma STCellRangeMax_replace_other :
  forall l st K row col idx v,
    STCellRangeMax l st K row col ->
    0 <= idx < Zlength st ->
    0 <= row * K + col < Zlength st ->
    idx <> row * K + col ->
    STCellRangeMax l (replace_Znth idx v st) K row col.
Proof.
  intros.
  unfold STCellRangeMax in *.
  rewrite Znth_replace_Znth_Diff by auto.
  exact H.
Qed.

Lemma STBuiltBeforeLevel_replace_level_cell :
  forall l st K n level row v,
    STBuiltBeforeLevel l st K n level ->
    level < K ->
    0 <= row * K + level < Zlength st ->
    (forall row0 col,
      0 <= row0 /\ 0 <= col /\ col < level /\ row0 + Power2 col <= n ->
      0 <= row0 * K + col < Zlength st) ->
    STBuiltBeforeLevel l (replace_Znth (row * K + level) v st) K n level.
Proof.
  intros.
  unfold STBuiltBeforeLevel in *.
  intros row0 col Hcell_args.
  eapply STCellRangeMax_replace_other.
  - apply H; exact Hcell_args.
  - exact H1.
  - apply H2; exact Hcell_args.
  - destruct Hcell_args as [Hrow0 [Hcol0 [Hcollt _]]].
    apply cell_index_diff_col_neq with (K := K); lia.
Qed.

Lemma RangeMaxValue_join_max :
  forall l i j half a b,
    1 <= j ->
    half = Power2 (j - 1) ->
    RangeMaxValue l i (i + Power2 (j - 1)) a ->
    RangeMaxValue l (i + half) (i + half + Power2 (j - 1)) b ->
    RangeMaxValue l i (i + Power2 j) (Z.max a b).
Proof.
  intros l i j half a b Hj Hhalf Hleft Hright.
  unfold RangeMaxValue in *.
  destruct Hleft as [Hi0 [Hilt1 [Hhi1 Hmax1]]].
  destruct Hright as [Hi20 [Hilt2 [Hhi2 Hmax2]]].
  repeat split.
  - exact Hi0.
  - pose proof (Power2_pos j ltac:(lia)); lia.
  - rewrite (Power2_sub1_double j) by lia.
    rewrite Hhalf in *; lia.
  - assert (Hcover : forall x : Z,
      (i <= x < i + Power2 (j - 1) \/
       i + half <= x < i + half + Power2 (j - 1)) <->
      i <= x < i + Power2 j).
    { intro x.
      rewrite (Power2_sub1_double j) by lia.
      rewrite Hhalf in *.
      split.
      - intros [[? ?] | [? ?]]; lia.
      - intros [? ?].
        destruct (Z_lt_ge_dec x (i + half)); [left | right]; lia.
    }
    pose proof (@MaxMin.max_union Z Z.le Interface.Zle_TotalOrder Z
      a b (fun x : Z => Znth x l 0)
      (fun x : Z => i <= x < i + Power2 (j - 1))
      (fun x : Z => i + half <= x < i + half + Power2 (j - 1))
      (fun x : Z => i <= x < i + Power2 j)
      Hmax1 Hmax2 Hcover) as Hmax.
    replace (MaxMin.le_max Z.le a b) with (Z.max a b) in Hmax by
      (unfold MaxMin.le_max; simpl;
       destruct (Interface.Z_le_total a b) as [Hab | Hba];
       [rewrite Z.max_r by lia | rewrite Z.max_l by lia]; reflexivity).
    exact Hmax.
Qed.

Lemma RangeMaxValue_join_left :
  forall l i j half a b,
    1 <= j ->
    half = Power2 (j - 1) ->
    a >= b ->
    RangeMaxValue l i (i + Power2 (j - 1)) a ->
    RangeMaxValue l (i + half) (i + half + Power2 (j - 1)) b ->
    RangeMaxValue l i (i + Power2 j) a.
Proof.
  intros l i j half a b Hj Hhalf Hge Hleft Hright.
  assert (Hmax : Z.max a b = a) by (apply Z.max_l; lia).
  rewrite <- Hmax.
  eapply RangeMaxValue_join_max; eauto.
Qed.

Lemma RangeMaxValue_join_right :
  forall l i j half a b,
    1 <= j ->
    half = Power2 (j - 1) ->
    a < b ->
    RangeMaxValue l i (i + Power2 (j - 1)) a ->
    RangeMaxValue l (i + half) (i + half + Power2 (j - 1)) b ->
    RangeMaxValue l i (i + Power2 j) b.
Proof.
  intros l i j half a b Hj Hhalf Hlt Hleft Hright.
  assert (Hmax : Z.max a b = b) by (apply Z.max_r; lia).
  rewrite <- Hmax.
  eapply RangeMaxValue_join_max; eauto.
Qed.

Lemma STCellRangeMax_extend_by_left_max :
  forall l st K i j half a b,
    1 <= j ->
    half = Power2 (j - 1) ->
    0 <= i * K + j < Zlength st ->
    a = Znth (i * K + (j - 1)) st 0 ->
    b = Znth ((i + half) * K + (j - 1)) st 0 ->
    a >= b ->
    STCellRangeMax l st K i (j - 1) ->
    STCellRangeMax l st K (i + half) (j - 1) ->
    STCellRangeMax l (replace_Znth (i * K + j) a st) K i j.
Proof.
  intros l st K i j half a b Hj Hhalf Hidx Ha Hb Hge Hleft Hright.
  unfold STCellRangeMax in *.
  rewrite <- Ha in Hleft.
  rewrite <- Hb in Hright.
  rewrite Znth_replace_Znth_Same by exact Hidx.
  eapply RangeMaxValue_join_left; eauto.
Qed.

Lemma STCellRangeMax_extend_by_right_max :
  forall l st K i j half a b,
    1 <= j ->
    half = Power2 (j - 1) ->
    0 <= i * K + j < Zlength st ->
    a = Znth (i * K + (j - 1)) st 0 ->
    b = Znth ((i + half) * K + (j - 1)) st 0 ->
    a < b ->
    STCellRangeMax l st K i (j - 1) ->
    STCellRangeMax l st K (i + half) (j - 1) ->
    STCellRangeMax l (replace_Znth (i * K + j) b st) K i j.
Proof.
  intros l st K i j half a b Hj Hhalf Hidx Ha Hb Hlt Hleft Hright.
  unfold STCellRangeMax in *.
  rewrite <- Ha in Hleft.
  rewrite <- Hb in Hright.
  rewrite Znth_replace_Znth_Same by exact Hidx.
  eapply RangeMaxValue_join_right; eauto.
Qed.

Lemma STLevelPrefix_extend_by_left_max :
  forall l st K n j i half a b,
    1 <= j ->
    j < K ->
    half = Power2 (j - 1) ->
    0 <= i * K + j < Zlength st ->
    a = Znth (i * K + (j - 1)) st 0 ->
    b = Znth ((i + half) * K + (j - 1)) st 0 ->
    a >= b ->
    STLevelPrefix l st K n j i ->
    STCellRangeMax l st K i (j - 1) ->
    STCellRangeMax l st K (i + half) (j - 1) ->
    STLevelPrefix l (replace_Znth (i * K + j) a st) K n j (i + 1).
Proof.
  intros l st K n j i half a b Hj HjK Hhalf Hidx Ha Hb Hge Hpref Hleft Hright.
  unfold STLevelPrefix in *.
  intros row Hrow.
  destruct Hrow as [Hrow0 [Hrowlt Hrowlen]].
  assert (row < i \/ row = i) as [Hlt | Heq] by lia.
  - eapply STCellRangeMax_replace_other.
    + apply Hpref; repeat split; lia.
    + exact Hidx.
    + split; nia.
    + apply cell_index_same_col_neq; lia.
  - subst row.
    eapply STCellRangeMax_extend_by_left_max; eauto.
Qed.

Lemma STLevelPrefix_extend_by_right_max :
  forall l st K n j i half a b,
    1 <= j ->
    j < K ->
    half = Power2 (j - 1) ->
    0 <= i * K + j < Zlength st ->
    a = Znth (i * K + (j - 1)) st 0 ->
    b = Znth ((i + half) * K + (j - 1)) st 0 ->
    a < b ->
    STLevelPrefix l st K n j i ->
    STCellRangeMax l st K i (j - 1) ->
    STCellRangeMax l st K (i + half) (j - 1) ->
    STLevelPrefix l (replace_Znth (i * K + j) b st) K n j (i + 1).
Proof.
  intros l st K n j i half a b Hj HjK Hhalf Hidx Ha Hb Hltab Hpref Hleft Hright.
  unfold STLevelPrefix in *.
  intros row Hrow.
  destruct Hrow as [Hrow0 [Hrowlt Hrowlen]].
  assert (row < i \/ row = i) as [Hlt | Heq] by lia.
  - eapply STCellRangeMax_replace_other.
    + apply Hpref; repeat split; lia.
    + exact Hidx.
    + split; nia.
    + apply cell_index_same_col_neq; lia.
  - subst row.
    eapply STCellRangeMax_extend_by_right_max; eauto.
Qed.

Lemma STLevelPrefix_exit_to_built_step :
  forall (l st_ls : list Z) (K n j upto len : Z),
    STBuiltBeforeLevel l st_ls K n j ->
    STLevelPrefix l st_ls K n j upto ->
    len = Power2 j ->
    upto + len > n ->
    STBuiltBeforeLevel l st_ls K n (j + 1).
Proof.
  intros l st_ls K n j upto len Hbuilt_before Hprefix Hlen Hexit.
  unfold STBuiltBeforeLevel, STLevelPrefix in *.
  intros p q Hcell_bound.
  destruct Hcell_bound as (Hp_nonneg & Hq_nonneg & Hq_lt_next & Hp_range).
  destruct (Z_lt_dec q j) as [Hq_lt_j | Hq_ge_j].
  - apply Hbuilt_before.
    repeat split; lia.
  - assert (q = j) by lia.
    subst q.
    assert (p < upto) by (rewrite <- Hlen in Hp_range; lia).
    apply Hprefix.
    repeat split; lia.
Qed.

Lemma Power2_step :
  forall j : Z, 0 <= j -> Power2 j * 2 = Power2 (j + 1).
Proof.
  intros j Hj.
  unfold Power2.
  rewrite Z.pow_add_r by lia.
  simpl.
  change (Z.pow_pos 2 1) with 2.
  reflexivity.
Qed.

Lemma Power2_step_query : forall k,
  0 <= k ->
  Power2 (k + 1) = Power2 k * 2.
Proof.
  intros k Hk.
  unfold Power2.
  rewrite Z.pow_add_r by lia.
  simpl.
  lia.
Qed.

Lemma QueryLogBounds_init : forall K n left right,
  1 <= n ->
  1 <= K ->
  n < Power2 K ->
  0 <= left ->
  left <= right ->
  right < n ->
  QueryLogBounds K n (right - left + 1) 0 1.
Proof.
  intros K n left right Hn HK Hpow Hleft Hle Hright.
  unfold QueryLogBounds, Power2 in *.
  simpl in *.
  lia.
Qed.

Lemma QueryLogLoopState_init : forall left right,
  0 <= left ->
  left <= right ->
  QueryLogLoopState (right - left + 1) 0 1.
Proof.
  intros left right Hleft Hle.
  unfold QueryLogLoopState, Power2.
  simpl.
  lia.
Qed.

Lemma QueryLogBounds_step : forall K n len k pow,
  pow * 2 <= len ->
  QueryLogBounds K n len k pow ->
  QueryLogLoopState len k pow ->
  QueryLogBounds K n len (k + 1) (pow * 2).
Proof.
  intros K n len k pow Hpow_len Hbounds Hstate.
  unfold QueryLogBounds in Hbounds |- *.
  unfold QueryLogLoopState in Hstate.
  destruct Hbounds as
    (Hlen_pos & Hlen_n & HK_pos & Hn_pow & Hk_pos & Hk_lt & Hpow_pos).
  destruct Hstate as (Hk_nonneg & Hpow & Hpow_le).
  assert (Hnext_eq : Power2 (k + 1) = Power2 k * 2) by
    (apply Power2_step_query; lia).
  assert (Hnext_le : Power2 (k + 1) <= len) by
    (rewrite Hnext_eq; rewrite <- Hpow; lia).
  assert (Hk_next_lt : k + 1 < K).
  {
    assert (Hk_next_le : k + 1 <= K) by lia.
    destruct (Z_lt_ge_dec (k + 1) K) as [Hlt | Hge]; [lia |].
    assert (k + 1 = K) by lia.
    subst K.
    lia.
  }
  repeat split; try lia.
Qed.

Lemma QueryLogLoopState_step : forall len k pow,
  pow * 2 <= len ->
  QueryLogLoopState len k pow ->
  QueryLogLoopState len (k + 1) (pow * 2).
Proof.
  intros len k pow Hpow_len Hstate.
  unfold QueryLogLoopState in Hstate |- *.
  destruct Hstate as (Hk_nonneg & Hpow & Hpow_le).
  assert (Hnext_eq : Power2 (k + 1) = Power2 k * 2) by
    (apply Power2_step_query; lia).
  split.
  - lia.
  - split.
    + rewrite Hnext_eq, <- Hpow; lia.
    + rewrite Hnext_eq, <- Hpow; lia.
Qed.

Lemma RangeMaxValue_sparse_query_max :
  forall (l st_l : list Z) (K n len left right j pow a b : Z),
    len = right - left + 1 ->
    a = Znth (left * K + j) st_l 0 ->
    b = Znth ((right - pow + 1) * K + j) st_l 0 ->
    QueryLogFinalState len j pow ->
    STCellRangeMax l st_l K left j ->
    STCellRangeMax l st_l K (right - pow + 1) j ->
    RangeMaxValue l left (right + 1) (Z.max a b).
Proof.
  intros l st_l K n len left right j pow a b Hlen Ha Hb Hq HcellL HcellR.
  unfold QueryLogFinalState, QueryLogLoopState in Hq.
  destruct Hq as [[Hj_nonneg [Hpow Hpow_le]] Hlen_pow_next].
  unfold STCellRangeMax in HcellL, HcellR.
  unfold RangeMaxValue in HcellL, HcellR.
  destruct HcellL as [HL0 [HLlt [HLhi HmaxL]]].
  destruct HcellR as [HR0 [HRlt [HRhi HmaxR]]].
  rewrite <- Ha in HmaxL.
  rewrite <- Hb in HmaxR.
  rewrite <- Hpow in HmaxL.
  rewrite <- Hpow in HmaxR.
  replace (right - pow + 1 + pow) with (right + 1) in HmaxR by lia.
  assert (Hpow_next : Power2 (j + 1) = 2 * pow).
  { rewrite Hpow. unfold Power2. rewrite Z.pow_add_r by lia.
    change (2 ^ 1) with 2; lia. }
  assert (Hcover : forall x : Z,
    (left <= x < left + pow \/ right - pow + 1 <= x < right + 1) <->
    left <= x < right + 1).
  { intro x; split.
    - intros [[? ?] | [? ?]]; lia.
    - intros [? ?]. destruct (Z_lt_ge_dec x (left + pow)) as [Hxlt | Hxge].
      + left; lia.
      + right; lia.
  }
  unfold RangeMaxValue.
  repeat split; try lia.
  pose proof (@MaxMin.max_union Z Z.le Interface.Zle_TotalOrder Z
    a b (fun x : Z => Znth x l 0)
    (fun x : Z => left <= x < left + pow)
    (fun x : Z => right - pow + 1 <= x < right + 1)
    (fun x : Z => left <= x < right + 1)
    HmaxL HmaxR Hcover) as Hmax.
  replace (MaxMin.le_max Z.le a b) with (Z.max a b) in Hmax by
    (unfold MaxMin.le_max; simpl;
     destruct (Interface.Z_le_total a b) as [Hab | Hba];
     [rewrite Z.max_r by lia | rewrite Z.max_l by lia]; reflexivity).
  exact Hmax.
Qed.

Lemma RangeMaxValue_sparse_query_left :
  forall (l st_l : list Z) (K n len left right j pow a b : Z),
    len = right - left + 1 ->
    a = Znth (left * K + j) st_l 0 ->
    b = Znth ((right - pow + 1) * K + j) st_l 0 ->
    QueryLogFinalState len j pow ->
    STCellRangeMax l st_l K left j ->
    STCellRangeMax l st_l K (right - pow + 1) j ->
    a >= b ->
    RangeMaxValue l left (right + 1) a.
Proof.
  intros l st_l K n len left right j pow a b Hlen Ha Hb Hq HcellL HcellR Hab.
  assert (Hmax : Z.max a b = a) by (apply Z.max_l; lia).
  rewrite <- Hmax.
  eapply RangeMaxValue_sparse_query_max; eauto.
Qed.

Lemma RangeMaxValue_sparse_query_right :
  forall (l st_l : list Z) (K n len left right j pow a b : Z),
    len = right - left + 1 ->
    a = Znth (left * K + j) st_l 0 ->
    b = Znth ((right - pow + 1) * K + j) st_l 0 ->
    QueryLogFinalState len j pow ->
    STCellRangeMax l st_l K left j ->
    STCellRangeMax l st_l K (right - pow + 1) j ->
    a < b ->
    RangeMaxValue l left (right + 1) b.
Proof.
  intros l st_l K n len left right j pow a b Hlen Ha Hb Hq HcellL HcellR Hab.
  assert (Hmax : Z.max a b = b) by (apply Z.max_r; lia).
  rewrite <- Hmax.
  eapply RangeMaxValue_sparse_query_max; eauto.
Qed.
