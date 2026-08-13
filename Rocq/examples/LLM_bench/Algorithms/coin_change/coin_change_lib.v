Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive ReachableAmount (coins : list Z) : Z -> Prop :=
  | ReachableAmount_zero :
      ReachableAmount coins 0
  | ReachableAmount_add :
      forall v c,
        ReachableAmount coins v ->
        In c coins ->
        0 < c ->
        ReachableAmount coins (v + c).

Definition MaxReachableAmount (coins : list Z) (amount ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun v => ReachableAmount coins v /\ 0 <= v /\ v <= amount)
    (fun v => v)
    ans.

Definition DpPrefixZeroed (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\
  Zlength dp >= hi /\
  Znth 0 dp 0 = 1 /\
  forall k, 1 <= k < hi -> Znth k dp 0 = 0.

Definition DpReachableTable (coins : list Z) (dp : list Z) (hi : Z) : Prop :=
  0 <= hi /\
  Zlength dp >= hi /\
  forall k, 0 <= k < hi -> (Znth k dp 0 <> 0 <-> ReachableAmount coins k).

Definition DpCoinInnerProgress
    (prev_coins : list Z) (coin : Z) (dp : list Z) (j amount : Z) : Prop :=
  0 < coin /\
  coin <= j /\
  j <= amount + 1 /\
  Zlength dp >= amount + 1 /\
  (forall k,
    0 <= k < j ->
    (Znth k dp 0 <> 0 <->
       ReachableAmount (app prev_coins (cons coin nil)) k)) /\
  forall k,
    j <= k < amount + 1 ->
    (Znth k dp 0 <> 0 <-> ReachableAmount prev_coins k).

Definition NoReachableAbove
    (coins : list Z) (amount res : Z) : Prop :=
  0 <= res <= amount /\
  forall k, res < k <= amount -> ~ ReachableAmount coins k.

Require Import Coq.micromega.Psatz.

(* Helper lemmas migrated from coin_change__vc_proving_subagent_tmp_proof_manual__merged_proof_manual.v. *)

Lemma MaxReachableAmount_intro_no_above :
  forall coins amount res,
    ReachableAmount coins res ->
    0 <= res ->
    res <= amount ->
    NoReachableAbove coins amount res ->
    MaxReachableAmount coins amount res.
Proof.
  intros coins amount res Hreach Hres_nonneg Hres_le Hnoabove.
  unfold MaxReachableAmount, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists res.
  split.
  - split.
    + split; [exact Hreach | lia].
    + intros b Hb.
      destruct Hb as [Hb_reach [_ Hb_le]].
      destruct (Z_le_gt_dec b res) as [Hb_res | Hb_gt]; [lia |].
      exfalso.
      unfold NoReachableAbove in Hnoabove.
      destruct Hnoabove as [_ Habove].
      apply (Habove b); [lia | exact Hb_reach].
  - reflexivity.
Qed.

Lemma ReachableAmount_nil_inv :
  forall v, ReachableAmount nil v -> v = 0.
Proof.
  intros v Hreach.
  remember (@nil Z) as coins eqn:Hcoins.
  induction Hreach; subst; auto.
  contradiction.
Qed.

Lemma DpPrefixZeroed_snoc_zero :
  forall dp j,
    0 < j ->
    DpPrefixZeroed dp j ->
    Zlength (dp ++ 0 :: nil) = j + 1 ->
    DpPrefixZeroed (dp ++ 0 :: nil) (j + 1).
Proof.
  intros dp j Hj Hpref Hlen_snoc.
  assert (Hlendp : Zlength dp = j) by
    (rewrite Zlength_app_cons in Hlen_snoc; lia).
  unfold DpPrefixZeroed in *.
  destruct Hpref as [Hj0 [Hlen [Hzero Hzeros]]].
  repeat split; try lia.
  - rewrite app_Znth1; auto; lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k j) as [Hlt | Hge].
    + rewrite app_Znth1; [apply Hzeros; lia | lia].
    + assert (k = j) by lia; subst k.
      rewrite app_Znth2; [| lia].
      replace (j - Zlength dp) with 0 by lia.
      reflexivity.
Qed.

Lemma DpPrefixZeroed_to_DpReachableTable_nil :
  forall dp hi,
    DpPrefixZeroed dp hi ->
    DpReachableTable nil dp hi.
Proof.
  intros dp hi Hpref.
  unfold DpPrefixZeroed in Hpref.
  unfold DpReachableTable.
  destruct Hpref as [Hhi [Hlen [Hzero Hzeros]]].
  split; [lia |].
  split; [lia |].
  intros idx Hidx.
  split; intro H.
  - destruct (Z.eq_dec idx 0) as [-> | Hnz].
    + constructor.
    + rewrite Hzeros in H by lia.
      contradiction.
  - apply ReachableAmount_nil_inv in H.
    subst idx.
    rewrite Hzero.
    lia.
Qed.

Lemma ReachableAmount_nonneg :
  forall coins v, ReachableAmount coins v -> 0 <= v.
Proof.
  intros coins v H.
  induction H; lia.
Qed.

Lemma ReachableAmount_mono_incl :
  forall coins1 coins2 v,
    (forall c, In c coins1 -> In c coins2) ->
    ReachableAmount coins1 v ->
    ReachableAmount coins2 v.
Proof.
  intros coins1 coins2 v Hincl Hreach.
  induction Hreach.
  - constructor.
  - eapply ReachableAmount_add; eauto.
Qed.

Lemma ReachableAmount_app_single_below :
  forall coins coin k,
    0 < coin ->
    0 <= k < coin ->
    (ReachableAmount (coins ++ coin :: nil) k <-> ReachableAmount coins k).
Proof.
  intros coins coin k Hcoin Hk.
  split.
  - intros Hreach.
    induction Hreach as [|v c Hreach IHHreach Hin Hc].
    + constructor.
    + apply in_app_or in Hin as [Hin | Hin].
      * eapply ReachableAmount_add; eauto.
        apply IHHreach.
        split.
        -- eapply ReachableAmount_nonneg; eauto.
        -- lia.
      * simpl in Hin. destruct Hin as [-> | []].
        assert (0 <= v) by (eapply ReachableAmount_nonneg; eauto).
        lia.
  - apply ReachableAmount_mono_incl.
    intros c Hin.
    apply in_or_app; auto.
Qed.

Lemma DpCoinInnerProgress_replace_current :
  forall prev coin dp j amount,
    Znth (j - coin) dp 0 <> 0 ->
    j <= amount ->
    DpCoinInnerProgress prev coin dp j amount ->
    DpCoinInnerProgress prev coin (replace_Znth j 1 dp) (j + 1) amount.
Proof.
  intros prev coin dp j amount Hprev Hj_amount Hprogress.
  unfold DpCoinInnerProgress in *.
  destruct Hprogress as
    [Hcoin_pos [Hcoin_le_j [Hj_le [Hlen [Hbefore Hafter]]]]].
  assert (Hj_bounds : 0 <= j < Zlength dp) by lia.
  repeat split; try lia.
  - rewrite Zlength_replace_Znth; lia.
  - intro Hnz.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + assert (Hjm : 0 <= j - coin < j) by lia.
      pose proof (proj1 (Hbefore (j - coin) Hjm) Hprev) as Hreach_prev.
      replace j with ((j - coin) + coin) by lia.
      eapply ReachableAmount_add with (v := j - coin) (c := coin); eauto.
      apply in_or_app. right. simpl. auto.
    + assert (Hklt : 0 <= k < j) by lia.
      rewrite Znth_replace_Znth_Diff in Hnz by lia.
      apply (proj1 (Hbefore k Hklt)).
      exact Hnz.
  - intro Hreach.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      lia.
    + assert (Hklt : 0 <= k < j) by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply (proj2 (Hbefore k Hklt)).
      exact Hreach.
  - intro Hnz.
    rewrite Znth_replace_Znth_Diff in Hnz by lia.
    apply (proj1 (Hafter k ltac:(lia))).
    exact Hnz.
  - intro Hreach.
    rewrite Znth_replace_Znth_Diff by lia.
    apply (proj2 (Hafter k ltac:(lia))).
    exact Hreach.
Qed.

Lemma ReachableAmount_app_l :
  forall coins extra v,
    ReachableAmount coins v ->
    ReachableAmount (app coins extra) v.
Proof.
  intros coins extra v H.
  induction H.
  - constructor.
  - eapply ReachableAmount_add; eauto.
    apply in_or_app; left; assumption.
Qed.

Lemma ReachableAmount_app_single_inv :
  forall prev coin v,
    0 < coin ->
    ReachableAmount (app prev (cons coin nil)) v ->
    ReachableAmount prev v \/
    (coin <= v /\
     ReachableAmount (app prev (cons coin nil)) (v - coin)).
Proof.
  intros prev coin v Hcoin Hreach.
  induction Hreach as [| v c Hreach IH Hin Hc].
  - left; constructor.
  - destruct (in_app_or _ _ _ Hin) as [Hinprev | Hsingle].
    + destruct IH as [Hprev | [Hle Hminus]].
      * left.
        eapply ReachableAmount_add; eauto.
      * right; split; [lia |].
        replace (v + c - coin) with ((v - coin) + c) by lia.
        eapply ReachableAmount_add; eauto.
    + simpl in Hsingle.
      destruct Hsingle as [Hceq | []].
      subst c.
      right; split.
      * pose proof (ReachableAmount_nonneg _ _ Hreach); lia.
      * replace (v + coin - coin) with v by lia.
        exact Hreach.
Qed.

Lemma ReachableAmount_app_single_lt :
  forall prev coin v,
    0 < coin ->
    v < coin ->
    ReachableAmount (app prev (cons coin nil)) v ->
    ReachableAmount prev v.
Proof.
  intros prev coin v Hcoin Hlt Hreach.
  pose proof (ReachableAmount_app_single_inv prev coin v Hcoin Hreach)
    as [Hprev | [Hle _]]; [assumption | lia].
Qed.

Lemma sublist_0_succ_app :
  forall {A : Type} (d : A) (l : list A) (i : Z),
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = app (sublist 0 i l) (cons (Znth i l d) nil).
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.
