Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition NonAdjacentIndexList (limit : Z) (picks : list Z) : Prop :=
  0 <= limit /\
  NoDup picks /\
  Forall (fun i => 0 <= i < limit) picks /\
  (forall i j,
      In i picks ->
      In j picks ->
      i <> j ->
      2 <= Z.abs (i - j)).

Definition RobPlanValue (l : list Z) (picks : list Z) : Z :=
  sum (map (fun i => Znth i l 0) picks).

Definition RobPrefixValue (l : list Z) (len value : Z) : Prop :=
  exists picks,
    0 <= len <= Zlength l /\
    NonAdjacentIndexList len picks /\
    value = RobPlanValue l picks.

Definition RobPrefixOpt (l : list Z) (len answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => RobPrefixValue l len value)
    (fun value => value)
    answer.

Definition HouseRobberAnswer (l : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun value => RobPrefixValue l (Zlength l) value)
    (fun value => value)
    answer.

Definition HouseRobberDPState
    (l : list Z) (i prev2 prev1 : Z) : Prop :=
  0 <= i <= Zlength l /\
  RobPrefixOpt l i prev1 /\
  ((i = 0 /\ prev2 = 0) \/
   (0 < i /\ RobPrefixOpt l (i - 1) prev2)).

(* Helper lemmas migrated from house_robber__vc_proving_subagent_tmp_proof_manual__merged_proof_manual.v. *)

Lemma RobPrefixOpt_zero : forall l, RobPrefixOpt l 0 0.
Proof.
  intros l.
  unfold RobPrefixOpt, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists 0. split; [split | reflexivity].
  - unfold RobPrefixValue. exists nil. split.
    + pose proof (Zlength_nonneg l). lia.
    + split.
      * unfold NonAdjacentIndexList. repeat split.
        -- lia.
        -- constructor.
        -- constructor.
        -- intros i j Hin. destruct Hin.
      * unfold RobPlanValue. simpl. reflexivity.
  - intros b Hb.
    unfold RobPrefixValue in Hb.
    destruct Hb as [picks [[Hlen_low Hlen_high] [HNA Hval]]].
    destruct HNA as [_ [_ [HForall _]]].
    destruct picks as [| i picks].
    + unfold RobPlanValue in Hval. simpl in Hval. subst. lia.
    + inversion HForall as [| x xs Hrange HForall_tail]; subst. lia.
Qed.

Lemma rob_prefix_opt_elim :
  forall l len answer,
    RobPrefixOpt l len answer ->
    RobPrefixValue l len answer /\
    (forall value, RobPrefixValue l len value -> value <= answer).
Proof.
  intros l len answer H.
  unfold RobPrefixOpt in H.
  unfold MaxMin.max_value_of_subset in H.
  destruct H as [a [Hmax Heq]].
  unfold MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [Hin Hle].
  subst answer.
  simpl in Hin, Hle.
  split; auto.
Qed.

Lemma rob_prefix_opt_intro :
  forall l len answer,
    RobPrefixValue l len answer ->
    (forall value, RobPrefixValue l len value -> value <= answer) ->
    RobPrefixOpt l len answer.
Proof.
  intros l len answer Hval Hmax.
  unfold RobPrefixOpt, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists answer.
  split.
  - split; simpl; auto.
  - reflexivity.
Qed.

Lemma rob_plan_value_nonneg_bound :
  forall l n picks,
    (forall k, 0 <= k < n -> 0 <= Znth k l 0 <= 10000) ->
    Forall (fun i => 0 <= i < n) picks ->
    0 <= RobPlanValue l picks /\
    RobPlanValue l picks <= 10000 * Z.of_nat (length picks).
Proof.
  intros l n picks Hrange Hforall.
  induction picks as [| x picks IH].
  - change (RobPlanValue l nil) with 0; simpl; lia.
  - inversion Hforall as [| ? ? Hx Hpicks]; subst.
    specialize (Hrange x Hx).
    specialize (IH Hpicks).
    destruct IH as [IHlo IHhi].
    change (RobPlanValue l (x :: picks)) with
      (Znth x l 0 + RobPlanValue l picks).
    replace (Z.of_nat (length (x :: picks))) with
      (Z.of_nat (length picks) + 1) by (simpl; lia).
    lia.
Qed.

Lemma NoDup_remove_Z :
  forall (x : Z) (l : list Z),
    NoDup l -> NoDup (remove Z.eq_dec x l).
Proof.
  intros x l Hnd.
  induction Hnd as [| a l Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (Z.eq_dec x a).
    + exact IH.
    + constructor; auto.
      intro Hin.
      apply in_remove in Hin as [Hin _].
      contradiction.
Qed.

Lemma NoDup_map_Z_to_nat :
  forall picks,
    Forall (fun i => 0 <= i) picks ->
    NoDup picks ->
    NoDup (map Z.to_nat picks).
Proof.
  intros picks Hnonneg Hnodup.
  induction picks as [| x picks IH]; simpl.
  - constructor.
  - inversion Hnonneg as [| ? ? Hx Hpicks_nonneg]; subst.
    inversion Hnodup as [| ? ? Hnotin Hpicks_nodup]; subst.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hin]].
      apply Hnotin.
      apply Z2Nat.inj in Hy; auto.
      * subst; auto.
      * apply Forall_forall with (x := y) in Hpicks_nonneg; auto.
    + apply IH; auto.
Qed.

Lemma NoDup_range_length :
  forall limit picks,
    0 <= limit ->
    NoDup picks ->
    Forall (fun i => 0 <= i < limit) picks ->
    Z.of_nat (length picks) <= limit.
Proof.
  intros limit picks Hlimit Hnodup Hforall.
  assert (Hnonneg : Forall (fun i => 0 <= i) picks).
  {
    eapply (Forall_impl (P := fun i => 0 <= i < limit)).
    - intros x Hx; lia.
    - exact Hforall.
  }
  pose proof (NoDup_map_Z_to_nat picks Hnonneg Hnodup) as Hmapnodup.
  assert (Hin_range : incl (map Z.to_nat picks) (seq 0 (Z.to_nat limit))).
  {
    intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as [z [Hz Hin]]; subst.
    apply in_seq.
    apply Forall_forall with (x := z) in Hforall; auto.
    lia.
  }
  pose proof (NoDup_incl_length Hmapnodup Hin_range) as Hlen.
  rewrite length_map in Hlen.
  rewrite length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.

Lemma rob_prefix_value_bound_by_len :
  forall l len value n,
    len <= n ->
    (forall k, 0 <= k < n -> 0 <= Znth k l 0 <= 10000) ->
    RobPrefixValue l len value ->
    0 <= value /\ value <= 10000 * len.
Proof.
  intros l len value n Hlen_le Hrange Hvalue.
  unfold RobPrefixValue in Hvalue.
  destruct Hvalue as [picks [Hlen [Hnonadj Hvalue]]].
  destruct Hlen as [Hlen_nonneg Hlen_bound].
  unfold NonAdjacentIndexList in Hnonadj.
  destruct Hnonadj as [Hlimit [Hnodup [Hforall Hdist]]].
  subst value.
  assert (Hforall_n : Forall (fun i => 0 <= i < n) picks).
  {
    eapply (Forall_impl (P := fun i => 0 <= i < len)).
    - intros x Hx; lia.
    - exact Hforall.
  }
  pose proof (rob_plan_value_nonneg_bound l n picks Hrange Hforall_n) as [Hnonneg Hsum_bound].
  pose proof (NoDup_range_length len picks Hlen_nonneg Hnodup Hforall) as Hpick_len.
  split; [exact Hnonneg | lia].
Qed.

Lemma rob_prefix_opt_bound_by_len :
  forall l len value n,
    len <= n ->
    (forall k, 0 <= k < n -> 0 <= Znth k l 0 <= 10000) ->
    RobPrefixOpt l len value ->
    0 <= value /\ value <= 10000 * len.
Proof.
  intros l len value n Hlen_le Hrange Hopt.
  destruct (rob_prefix_opt_elim l len value Hopt) as [Hvalue _].
  eapply rob_prefix_value_bound_by_len; eauto.
Qed.

Lemma nonadj_drop_last_notin :
  forall limit picks,
    0 <= limit ->
    NonAdjacentIndexList (limit + 1) picks ->
    ~ In limit picks ->
    NonAdjacentIndexList limit picks.
Proof.
  intros limit picks Hlimit Hnonadj Hnotin.
  unfold NonAdjacentIndexList in *.
  destruct Hnonadj as [_ [Hnodup [Hforall Hdist]]].
  split; [lia |].
  split; [exact Hnodup |].
  split.
  - apply Forall_forall.
    intros x Hin.
    apply Forall_forall with (x := x) in Hforall; auto.
    assert (x <> limit) by (intro; subst; contradiction).
    lia.
  - intros i j Hi Hj Hij.
    apply Hdist; auto.
Qed.

Lemma nonadj_single_zero :
  NonAdjacentIndexList 1 (0 :: nil).
Proof.
  unfold NonAdjacentIndexList.
  split; [lia |].
  split.
  - constructor; [intro Hin; inversion Hin | constructor].
  - split.
    + constructor; [lia | constructor].
    + intros i j Hi Hj Hij.
      simpl in Hi, Hj.
      destruct Hi as [Hi | []].
      destruct Hj as [Hj | []].
      subst; contradiction.
Qed.

Lemma nonadj_cons_current :
  forall i picks,
    0 < i ->
    NonAdjacentIndexList (i - 1) picks ->
    NonAdjacentIndexList (i + 1) (i :: picks).
Proof.
  intros i picks Hi_pos Hnonadj.
  unfold NonAdjacentIndexList in *.
  destruct Hnonadj as [Hlimit [Hnodup [Hforall Hdist]]].
  split; [lia |].
  split.
  - constructor; auto.
    intro Hin.
    apply Forall_forall with (x := i) in Hforall; auto.
    lia.
  - split.
    + constructor; [lia |].
      eapply (Forall_impl (P := fun x => 0 <= x < i - 1)).
      * intros x Hx; lia.
      * exact Hforall.
    + intros a b Ha Hb Hab.
      simpl in Ha, Hb.
      destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb]; subst; try contradiction.
      * apply Forall_forall with (x := b) in Hforall; auto.
        rewrite Z.abs_eq; lia.
      * apply Forall_forall with (x := a) in Hforall; auto.
        rewrite Z.abs_neq; lia.
      * apply Hdist; auto.
Qed.

Lemma nonadj_remove_current :
  forall i picks,
    0 < i ->
    In i picks ->
    NonAdjacentIndexList (i + 1) picks ->
    NonAdjacentIndexList (i - 1) (remove Z.eq_dec i picks).
Proof.
  intros i picks Hi_pos Hi_in Hnonadj.
  unfold NonAdjacentIndexList in *.
  destruct Hnonadj as [_ [Hnodup [Hforall Hdist]]].
  split; [lia |].
  split.
  - apply NoDup_remove_Z; auto.
  - split.
    + apply Forall_forall.
      intros x Hx.
      apply in_remove in Hx.
      destruct Hx as [Hx_in Hx_neq].
      apply Forall_forall with (x := x) in Hforall; auto.
      assert (i <> x) as Hineq by (intro Heq; subst; contradiction).
      pose proof (Hdist i x Hi_in Hx_in Hineq) as Habs.
      assert (x < i).
      {
        assert (x <= i) by lia.
        lia.
      }
      rewrite Z.abs_eq in Habs by lia.
      lia.
    + intros a b Ha Hb Hab.
      apply in_remove in Ha.
      apply in_remove in Hb.
      destruct Ha as [Ha_in _].
      destruct Hb as [Hb_in _].
      apply Hdist; auto.
Qed.

Lemma remove_zero_range_one_nil :
  forall picks,
    Forall (fun x => 0 <= x < 1) picks ->
    remove Z.eq_dec 0 picks = nil.
Proof.
  intros picks Hforall.
  destruct (remove Z.eq_dec 0 picks) as [| x xs] eqn:Hremove; auto.
  assert (Hin_remove : In x (remove Z.eq_dec 0 picks)).
  {
    rewrite Hremove; simpl; auto.
  }
  apply in_remove in Hin_remove.
  destruct Hin_remove as [Hin Hneq].
  apply Forall_forall with (x := x) in Hforall; auto.
  lia.
Qed.

Lemma rob_plan_value_remove :
  forall l x picks,
    NoDup picks ->
    In x picks ->
    RobPlanValue l picks =
    Znth x l 0 + RobPlanValue l (remove Z.eq_dec x picks).
Proof.
  intros l x picks Hnodup Hin.
  induction picks as [| y picks IH]; simpl in Hin; [contradiction |].
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  unfold RobPlanValue in *; simpl in *.
  destruct (Z.eq_dec x y) as [Heq | Hneq].
  - subst.
    rewrite notin_remove by auto.
    lia.
  - destruct Hin as [Hin | Hin]; [subst; congruence |].
    specialize (IH Hnodup_tail Hin).
    unfold RobPlanValue in IH; simpl in IH.
    simpl.
    lia.
Qed.

Lemma rob_prefix_step_take :
  forall l i prev2 prev1,
    0 <= i < Zlength l ->
    HouseRobberDPState l i prev2 prev1 ->
    prev1 < prev2 + Znth i l 0 ->
    RobPrefixOpt l (i + 1) (prev2 + Znth i l 0).
Proof.
  intros l i prev2 prev1 Hi_range Hstate Htake_gt.
  unfold HouseRobberDPState in Hstate.
  destruct Hstate as [Hi_state [Hopt_i Hprev2_case]].
  apply rob_prefix_opt_intro.
  - destruct Hprev2_case as [[Hi_zero Hprev2_zero] | [Hi_pos Hopt_prev2]].
    + subst i prev2.
      unfold RobPrefixValue.
      exists (0 :: nil).
      split; [lia |].
      split; [apply nonadj_single_zero |].
      unfold RobPlanValue; simpl; lia.
    + destruct (rob_prefix_opt_elim l (i - 1) prev2 Hopt_prev2) as [Hprev2_value _].
      unfold RobPrefixValue in Hprev2_value.
      destruct Hprev2_value as [picks [Hlen [Hnonadj Hvalue]]].
      unfold RobPrefixValue.
      exists (i :: picks).
      split; [lia |].
      split.
      * apply nonadj_cons_current; auto.
      * rewrite Hvalue.
        unfold RobPlanValue; simpl; lia.
  - intros value Hvalue.
    unfold RobPrefixValue in Hvalue.
    destruct Hvalue as [picks [Hlen [Hnonadj Hvalue]]].
    subst value.
    destruct (in_dec Z.eq_dec i picks) as [Hi_in | Hi_notin].
    + pose proof Hnonadj as Hnonadj_orig.
      unfold NonAdjacentIndexList in Hnonadj.
      destruct Hnonadj as [Hlimit [Hnodup [Hforall Hdist]]].
      pose proof (rob_plan_value_remove l i picks Hnodup Hi_in) as Hremove_value.
      destruct (Z.eq_dec i 0) as [Hi_zero | Hi_nonzero].
      * subst i.
        assert (Hremove_nil : remove Z.eq_dec 0 picks = nil).
        {
          apply remove_zero_range_one_nil; auto.
        }
        rewrite Hremove_nil in Hremove_value.
        change (RobPlanValue l nil) with 0 in Hremove_value.
        destruct Hprev2_case as [[_ Hprev2_zero] | [Hpos _]]; [subst prev2 | lia].
        lia.
      * assert (Hi_pos : 0 < i) by lia.
        destruct Hprev2_case as [[Hzero _] | [_ Hopt_prev2]]; [lia |].
        destruct (rob_prefix_opt_elim l (i - 1) prev2 Hopt_prev2) as [_ Hmax_prev2].
        assert (Hremoved_prefix : RobPrefixValue l (i - 1) (RobPlanValue l (remove Z.eq_dec i picks))).
        {
          unfold RobPrefixValue.
          exists (remove Z.eq_dec i picks).
          split; [lia |].
          split.
          - apply nonadj_remove_current; auto.
          - reflexivity.
        }
        specialize (Hmax_prev2 _ Hremoved_prefix).
        lia.
    + assert (Hnonadj_i : NonAdjacentIndexList i picks).
      {
        apply nonadj_drop_last_notin.
        - lia.
        - exact Hnonadj.
        - exact Hi_notin.
      }
      destruct (rob_prefix_opt_elim l i prev1 Hopt_i) as [_ Hmax_i].
      assert (Hprefix_i : RobPrefixValue l i (RobPlanValue l picks)).
      {
        unfold RobPrefixValue.
        exists picks.
        split; [lia |].
        split; auto.
      }
      specialize (Hmax_i _ Hprefix_i).
      lia.
Qed.

Lemma house_robber_dp_step_take :
  forall l n i prev2 prev1,
    Zlength l = n ->
    0 <= i ->
    i < n ->
    HouseRobberDPState l i prev2 prev1 ->
    prev2 + Znth i l 0 > prev1 ->
    HouseRobberDPState l (i + 1) prev1 (prev2 + Znth i l 0).
Proof.
  intros l n i prev2 prev1 Hlen Hi_nonneg Hi_lt Hstate Htake.
  pose proof Hstate as Hstate_orig.
  unfold HouseRobberDPState in *.
  destruct Hstate as [Hi_state [Hopt_i Hprev2_case]].
  split; [lia |].
  split.
  - apply (rob_prefix_step_take l i prev2 prev1); auto; lia.
  - right.
    split; [lia |].
    replace (i + 1 - 1) with i by lia.
    exact Hopt_i.
Qed.

Lemma house_robber_take_value_bound :
  forall l n i prev2 prev1,
    Zlength l = n ->
    n <= 100000 ->
    (forall k, 0 <= k < n -> 0 <= Znth k l 0 <= 10000) ->
    0 <= i ->
    i < n ->
    HouseRobberDPState l i prev2 prev1 ->
    prev2 + Znth i l 0 <= 1000000000.
Proof.
  intros l n i prev2 prev1 Hlen Hn_bound Hrange Hi_nonneg Hi_lt Hstate.
  unfold HouseRobberDPState in Hstate.
  destruct Hstate as [_ [_ Hprev2_case]].
  pose proof (Hrange i ltac:(lia)) as [_ Hcurrent_bound].
  destruct Hprev2_case as [[Hi_zero Hprev2_zero] | [Hi_pos Hopt_prev2]].
  - subst; lia.
  - pose proof (rob_prefix_opt_bound_by_len l (i - 1) prev2 n ltac:(lia) Hrange Hopt_prev2)
      as [_ Hprev2_bound].
    lia.
Qed.

Lemma NonAdjacentIndexList_extend :
  forall (limit1 limit2 : Z) (picks : list Z),
    limit1 <= limit2 ->
    NonAdjacentIndexList limit1 picks ->
    NonAdjacentIndexList limit2 picks.
Proof.
  intros limit1 limit2 picks Hle Hna.
  unfold NonAdjacentIndexList in *.
  destruct Hna as [Hlimit [Hnodup [Hbounds Hsep]]].
  repeat split; auto; try lia.
  eapply Forall_impl; [| exact Hbounds].
  intros a Ha.
  destruct Ha; lia.
Qed.

Lemma RobPrefixValue_extend :
  forall (l : list Z) (len value : Z),
    len < Zlength l ->
    RobPrefixValue l len value ->
    RobPrefixValue l (len + 1) value.
Proof.
  intros l len value Hlen Hval.
  unfold RobPrefixValue in *.
  destruct Hval as [picks [Hrange [Hna Hvalue]]].
  destruct Hrange as [Hlen0 HlenZ].
  exists picks.
  split; [lia | split].
  - eapply NonAdjacentIndexList_extend; eauto; lia.
  - exact Hvalue.
Qed.

Lemma NonAdjacentIndexList_drop_last_notin :
  forall (i : Z) (picks : list Z),
    0 <= i ->
    NonAdjacentIndexList (i + 1) picks ->
    ~ In i picks ->
    NonAdjacentIndexList i picks.
Proof.
  intros i picks Hi Hna Hnotin.
  unfold NonAdjacentIndexList in *.
  destruct Hna as [_ [Hnodup [Hbounds Hsep]]].
  repeat split; auto; try lia.
  apply Forall_forall.
  intros j Hj.
  rewrite Forall_forall in Hbounds.
  specialize (Hbounds j Hj).
  assert (j <> i) by (intro Heq; subst; contradiction).
  lia.
Qed.

Lemma NonAdjacentIndexList_remove_current :
  forall (i : Z) (picks : list Z),
    0 < i ->
    NonAdjacentIndexList (i + 1) picks ->
    In i picks ->
    NonAdjacentIndexList (i - 1) (remove Z.eq_dec i picks).
Proof.
  intros i picks Hi Hna Hin_i.
  unfold NonAdjacentIndexList in *.
  destruct Hna as [_ [Hnodup [Hbounds Hsep]]].
  repeat split; auto; try lia.
  - apply NoDup_remove_Z; auto.
  - apply Forall_forall.
    intros j Hj.
    apply in_remove in Hj as [Hj_in Hj_ne].
    rewrite Forall_forall in Hbounds.
    specialize (Hbounds j Hj_in).
    assert (2 <= Z.abs (j - i)) as Hfar.
    { apply Hsep; auto. }
    assert (j <= i) by lia.
    rewrite Z.abs_neq in Hfar by lia.
    lia.
  - intros a b Ha Hb Hab.
    apply in_remove in Ha as [Ha _].
    apply in_remove in Hb as [Hb _].
    apply Hsep; auto.
Qed.

Lemma RobPlanValue_remove_in :
  forall (l picks : list Z) (i : Z),
    NoDup picks ->
    In i picks ->
    RobPlanValue l picks =
      Znth i l 0 + RobPlanValue l (remove Z.eq_dec i picks).
Proof.
  intros l picks.
  induction picks as [| a picks IH]; intros i Hnd Hin; simpl in *.
  - contradiction.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    destruct Hin as [Hai | Hin].
    + subst a.
      destruct (Z.eq_dec i i) as [_ | Hneq]; [| contradiction].
      rewrite notin_remove by exact Hnotin.
      unfold RobPlanValue; simpl; lia.
    + destruct (Z.eq_dec i a) as [Heq | Hneq].
      * subst a; contradiction.
      * unfold RobPlanValue in *; simpl.
        rewrite (IH i Hnd' Hin).
        lia.
Qed.

Lemma RobPlanValue_limit_one_in :
  forall (l picks : list Z),
    NonAdjacentIndexList 1 picks ->
    In 0 picks ->
    RobPlanValue l picks = Znth 0 l 0.
Proof.
  intros l picks Hna Hin0.
  unfold NonAdjacentIndexList in Hna.
  destruct Hna as [_ [Hnodup [Hbounds _]]].
  rewrite (RobPlanValue_remove_in l picks 0 Hnodup Hin0).
  assert (remove Z.eq_dec 0 picks = nil) as Hremove_nil.
  { destruct (remove Z.eq_dec 0 picks) as [| j rest] eqn:Hremove; auto.
    assert (In j (remove Z.eq_dec 0 picks)).
    { rewrite Hremove; simpl; auto. }
    apply in_remove in H as [Hj_in Hj_ne].
    rewrite Forall_forall in Hbounds.
    specialize (Hbounds j Hj_in).
    lia. }
  rewrite Hremove_nil.
  unfold RobPlanValue; simpl; lia.
Qed.

Lemma RobPrefixValue_remove_current :
  forall (l : list Z) (i : Z) (picks : list Z),
    0 < i ->
    i + 1 <= Zlength l ->
    NonAdjacentIndexList (i + 1) picks ->
    In i picks ->
    RobPrefixValue l (i - 1) (RobPlanValue l (remove Z.eq_dec i picks)).
Proof.
  intros l i picks Hi Hlen Hna Hin.
  unfold RobPrefixValue.
  exists (remove Z.eq_dec i picks).
  split; [lia | split].
  - apply NonAdjacentIndexList_remove_current; auto.
  - reflexivity.
Qed.

Lemma RobPrefixOpt_step_skip :
  forall (l : list Z) (i prev2 prev1 : Z),
    RobPrefixOpt l i prev1 ->
    ((i = 0 /\ prev2 = 0) \/ (0 < i /\ RobPrefixOpt l (i - 1) prev2)) ->
    prev2 + Znth i l 0 <= prev1 ->
    i + 1 <= Zlength l ->
    RobPrefixOpt l (i + 1) prev1.
Proof.
  intros l i prev2 prev1 Hcur Hprev Hskip Hlen.
  unfold RobPrefixOpt, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hcur as [best [[Hbest Hmax] Hbest_eq]].
  subst best.
  exists prev1.
  split; [split | reflexivity].
  - eapply RobPrefixValue_extend; eauto.
    destruct Hbest as [_ [Hrange _]].
    lia.
  - intros v Hv.
    destruct Hv as [picks [Hrange [Hna Hv]]].
    subst v.
    destruct (in_dec Z.eq_dec i picks) as [Hin_i | Hnotin_i].
    + destruct Hprev as [[Hi0 Hprev0] | [Hi_pos Hprev_opt]].
      * subst i prev2.
        rewrite (RobPlanValue_limit_one_in l picks Hna Hin_i).
        lia.
      * unfold RobPrefixOpt, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hprev_opt.
        destruct Hprev_opt as [best_prev [[Hbest_prev Hmax_prev] Hbest_prev_eq]].
        subst best_prev.
        assert (Hremoved :
          RobPrefixValue l (i - 1) (RobPlanValue l (remove Z.eq_dec i picks))).
        { apply RobPrefixValue_remove_current; auto; lia. }
        specialize (Hmax_prev _ Hremoved).
        unfold NonAdjacentIndexList in Hna.
        destruct Hna as [_ [Hnodup _]].
        rewrite (RobPlanValue_remove_in l picks i Hnodup Hin_i).
        lia.
    + assert (Hsame : RobPrefixValue l i (RobPlanValue l picks)).
      { destruct Hbest as [best_picks [Hrange_best _]].
        destruct Hrange_best as [Hi0 HiZ].
        unfold RobPrefixValue.
        exists picks.
        split; [lia | split].
        - apply NonAdjacentIndexList_drop_last_notin; auto.
        - reflexivity. }
      apply Hmax in Hsame.
      exact Hsame.
Qed.

Lemma HouseRobberDPState_skip_step :
  forall (l : list Z) (i prev2 prev1 : Z),
    HouseRobberDPState l i prev2 prev1 ->
    prev2 + Znth i l 0 <= prev1 ->
    i + 1 <= Zlength l ->
    HouseRobberDPState l (i + 1) prev1 prev1.
Proof.
  intros l i prev2 prev1 Hstate Hskip Hlen.
  unfold HouseRobberDPState in *.
  destruct Hstate as [Hrange [Hcur Hprev]].
  split; [lia | split].
  - eapply RobPrefixOpt_step_skip; eauto.
  - right.
    split; [lia |].
    replace (i + 1 - 1) with i by lia.
    exact Hcur.
Qed.
