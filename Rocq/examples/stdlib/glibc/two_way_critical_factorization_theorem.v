Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Orders.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import ListLib.General.Presuffix.
From MonadLib Require Export MonadLib.
Export StateRelMonadErr.
Export MonadNotation.

From SimpleC.EE.stdlib.glibc Require Import two_way_rel_lib.
From SimpleC.EE.stdlib.glibc Require Import two_way_list_lemmas.

Import ListNotations.
Import SetsNotation.

Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.

(* Critical-factorization lemmas for the two_way high-level specification proof. *)

Definition skipn' {A : Type} (i : Z) (l : list A) : list A :=
  sublist i (Zlength l) l.

Definition is_maximal_suffix {A : Type}
    (cmp_fn : A -> A -> comparison) (l : list A) (pos : Z) : Prop :=
  0 <= pos <= Zlength l /\
  forall pos', 0 <= pos' <= Zlength l ->
    list_lex_ge A cmp_fn (skipn' pos l) (skipn' pos' l).

Instance Cmp_Zcompare : Cmp Z Z.compare.
Proof.
  constructor; intros.
  - apply Z.compare_lt_iff in H. apply Z.compare_gt_iff. exact H.
  - apply Z.compare_gt_iff in H. apply Z.compare_lt_iff. exact H.
  - apply Z.compare_eq_iff in H. subst. split; [reflexivity|apply Z.compare_refl].
  - apply Z.compare_refl.
  - apply Z.compare_gt_iff in H. apply Z.compare_gt_iff in H0.
    apply Z.compare_gt_iff. lia.
Qed.

Definition Z_compare_rev : Z -> Z -> comparison :=
  fun a b => Z.compare b a.

Instance Cmp_Zcompare_rev : Cmp Z Z_compare_rev.
Proof.
  constructor; intros.
  - unfold Z_compare_rev in *.
    apply Z.compare_lt_iff in H. apply Z.compare_gt_iff. exact H.
  - unfold Z_compare_rev in *.
    apply Z.compare_gt_iff in H. apply Z.compare_lt_iff. exact H.
  - unfold Z_compare_rev in *.
    apply Z.compare_eq_iff in H. subst. split; [reflexivity|apply Z.compare_refl].
  - unfold Z_compare_rev. apply Z.compare_refl.
  - unfold Z_compare_rev in *.
    apply Z.compare_gt_iff in H. apply Z.compare_gt_iff in H0.
    apply Z.compare_gt_iff. lia.
Qed.

Lemma Z_compare_rev_cmp_rev_eq (x y : Z) :
  Z_compare_rev x y = cmp_rev Z Z.compare x y.
Proof.
  unfold Z_compare_rev, cmp_rev.
  rewrite Z.compare_antisym.
  destruct (y ?= x); reflexivity.
Qed.

Lemma list_lex_ge_Z_compare_rev_as_cmp_rev (l1 l2 : list Z) :
  list_lex_ge Z Z_compare_rev l1 l2 ->
  list_lex_ge Z (cmp_rev Z Z.compare) l1 l2.
Proof.
  unfold list_lex_ge, list_lex_gt, list_lex_gt_ex.
  intros [Hgt | Heq].
  - left.
    destruct Hgt as [Hgtex | Hprefix].
    + left.
      destruct Hgtex as [p [x [y [l1' [l2' [H1 [H2 Hcmp]]]]]]].
      exists p, x, y, l1', l2'.
      repeat split; auto.
      rewrite <- Z_compare_rev_cmp_rev_eq.
      exact Hcmp.
    + right. exact Hprefix.
  - right. exact Heq.
Qed.

Section CriticalFactorizationMath.

Context (patn : list Z).
Context (patn_nonempty : patn <> nil).

Definition local_period (l w : Z) : Prop :=
  0 <= l <= Zlength patn /\
  0 < w /\
  forall i,
    0 <= i < w ->
    0 <= l + i - w < l ->
    l + i < Zlength patn ->
    Znth (l + i - w) patn 0 = Znth (l + i) patn 0.

Definition min_local_period (l w : Z) : Prop :=
  local_period l w /\ forall w', local_period l w' -> w' >= w.

Lemma local_period_existence :
  forall l, 0 <= l <= Zlength patn ->
    exists r, 0 < r <= Zlength patn /\ local_period l r.
Proof.
  intros l Hl.
  exists (Zlength patn).
  split.
  - pose proof Zlength_nonneg patn.
    destruct (Z.eq_dec (Zlength patn) 0) as [Hz | Hz]; [|lia].
    apply Zlength_nil_inv in Hz; contradiction.
  - unfold local_period.
    split; [lia|split].
    + pose proof Zlength_nonneg patn.
      destruct (Z.eq_dec (Zlength patn) 0) as [Hz | Hz]; [|lia].
      apply Zlength_nil_inv in Hz; contradiction.
    + intros; lia.
Qed.

Lemma nat_exists_min (P : nat -> Prop) :
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall n : nat, P n -> (m <= n)%nat.
Proof.
  intros [n0 Hn0].
  revert Hn0.
  pattern n0.
  apply lt_wf_ind.
  intros n IH Hn.
  destruct (classic (exists m : nat, (m < n)%nat /\ P m)) as [Hex|Hnomin].
  - destruct Hex as [m [Hm_lt HmP]].
    specialize (IH m Hm_lt HmP) as [mmin [HmminP Hmmin_le]].
    exists mmin. split; [exact HmminP|].
    intros k Hk; exact (Hmmin_le k Hk).
  - exists n. split; [exact Hn|].
    intros k Hk.
    assert (~ (k < n)%nat) as Hnotlt.
    { intro Hlt. apply Hnomin. exists k. split; auto. }
    lia.
Qed.

Lemma min_local_period_existence :
  forall l, 0 <= l <= Zlength patn ->
    exists r, 0 < r <= Zlength patn /\ min_local_period l r.
Proof.
  intros l Hl.
  destruct (local_period_existence l Hl) as [r0 [[Hr0_pos Hr0_le] Hr0_lp]].
  set (N := Z.to_nat (Zlength patn)).
  set (Pn := fun n : nat =>
              (0 < n)%nat /\
              (n <= N)%nat /\
              local_period l (Z.of_nat n)).
  assert (Hex : exists n, Pn n).
  { exists (Z.to_nat r0).
    assert (Hr0_ge0 : 0 <= r0) by lia.
    split.
    - apply (Z2Nat.inj_lt 0 r0); lia.
    - split.
      + unfold N. apply (Z2Nat.inj_le r0 (Zlength patn)); try lia.
      + rewrite (Z2Nat.id r0) by lia.
        exact Hr0_lp. }
  destruct (nat_exists_min Pn Hex) as [nmin [HnminP Hnmin_le]].
  set (r := Z.of_nat nmin).
  exists r.
  split.
  - destruct HnminP as [Hnpos [HnleN _]].
    split; [lia|].
    assert (Z.of_nat nmin <= Z.of_nat N) by (apply Nat2Z.inj_le; exact HnleN).
    unfold N in H.
    rewrite (Z2Nat.id (Zlength patn)) in H by (apply Zlength_nonneg).
    exact H.
  - unfold min_local_period.
    split.
    + destruct HnminP as [_ [_ Hlp]]. exact Hlp.
    + intros w' Hw'.
      assert (Hw'_pos : 0 < w') by (destruct Hw' as [_ [Hpos _]]; exact Hpos).
      destruct (Z_le_gt_dec w' (Zlength patn)) as [Hw'_le | Hw'_gt].
      * set (n' := Z.to_nat w').
        assert (HPn' : Pn n').
        { subst n'. split.
          - apply (Z2Nat.inj_lt 0 w'); lia.
          - split.
            + unfold N. apply (Z2Nat.inj_le w' (Zlength patn)); try lia.
            + rewrite (Z2Nat.id w') by lia.
              exact Hw'. }
        specialize (Hnmin_le n' HPn').
        assert (Z.of_nat nmin <= Z.of_nat n') by
          (apply Nat2Z.inj_le; exact Hnmin_le).
        subst r n'. rewrite (Z2Nat.id w') in H by lia. lia.
      * assert (Hr_le : r <= Zlength patn).
        { subst r.
          destruct HnminP as [_ [HnleN _]].
          apply Nat2Z.inj_le in HnleN.
          unfold N in HnleN.
          rewrite (Z2Nat.id (Zlength patn)) in HnleN by (apply Zlength_nonneg).
          exact HnleN. }
        lia.
Qed.

Lemma period_is_local_period (l r : Z) :
  0 <= l <= Zlength patn ->
  is_period 0 patn r ->
  local_period l r.
Proof.
  intros Hl Hper.
  destruct Hl as [Hl0 Hllen].
  unfold is_period in Hper.
  destruct Hper as [Hrpos Hper].
  unfold local_period.
  split; [lia|split; [lia|]].
  intros i Hi Hleft Hright.
  specialize (Hper (l + i - r) ltac:(lia) ltac:(lia)).
  replace (l + i - r + r) with (l + i) in Hper by lia.
  exact Hper.
Qed.

Lemma min_local_period_le_min_period (l r p : Z) :
  is_minimal_period 0 patn p ->
  min_local_period l r ->
  r <= p.
Proof.
  intros Hmin Hlocal.
  destruct Hlocal as [Hlocal Hleast].
  assert (Hlrange : 0 <= l <= Zlength patn).
  { unfold local_period in Hlocal. tauto. }
  destruct Hmin as [Hper Hglobal_min].
  pose proof period_is_local_period l p Hlrange Hper as Hplocal.
  specialize (Hleast p Hplocal).
  lia.
Qed.

Lemma period_existence :
  exists p, 0 < p <= Zlength patn /\ is_period 0 patn p.
Proof.
  exists (Zlength patn).
  split.
  - pose proof Zlength_nonneg patn.
    destruct (Z.eq_dec (Zlength patn) 0) as [Hz | Hz]; [|lia].
    apply Zlength_nil_inv in Hz; contradiction.
  - unfold is_period.
    split.
    + pose proof Zlength_nonneg patn.
      destruct (Z.eq_dec (Zlength patn) 0) as [Hz | Hz]; [|lia].
      apply Zlength_nil_inv in Hz; contradiction.
    + intros; lia.
Qed.

Lemma minimal_period_existence :
  exists p, 0 < p <= Zlength patn /\ is_minimal_period 0 patn p.
Proof.
  destruct period_existence as [p0 [[Hp0_pos Hp0_le] Hp0_period]].
  set (N := Z.to_nat (Zlength patn)).
  set (Pn := fun n : nat =>
              (0 < n)%nat /\
              (n <= N)%nat /\
              is_period 0 patn (Z.of_nat n)).
  assert (Hex : exists n, Pn n).
  { exists (Z.to_nat p0).
    split.
    - apply (Z2Nat.inj_lt 0 p0); lia.
    - split.
      + unfold N. apply (Z2Nat.inj_le p0 (Zlength patn)); try lia.
      + rewrite (Z2Nat.id p0) by lia.
        exact Hp0_period. }
  destruct (nat_exists_min Pn Hex) as [nmin [HnminP Hnmin_le]].
  set (p := Z.of_nat nmin).
  exists p.
  split.
  - destruct HnminP as [Hnpos [HnleN _]].
    split; [lia|].
    assert (Z.of_nat nmin <= Z.of_nat N) by (apply Nat2Z.inj_le; exact HnleN).
    unfold N in H.
    rewrite (Z2Nat.id (Zlength patn)) in H by (apply Zlength_nonneg).
    exact H.
  - unfold is_minimal_period.
    split.
    + destruct HnminP as [_ [_ Hper]]. exact Hper.
    + intros p' Hp'.
      destruct Hp' as [Hp'_pos Hp'_body].
      destruct (Z_le_gt_dec p' (Zlength patn)) as [Hp'_le | Hp'_gt].
      * set (n' := Z.to_nat p').
        assert (HPn' : Pn n').
        { subst n'. split.
          - apply (Z2Nat.inj_lt 0 p'); lia.
          - split.
            + unfold N. apply (Z2Nat.inj_le p' (Zlength patn)); try lia.
            + rewrite (Z2Nat.id p') by lia.
              split; auto. }
        specialize (Hnmin_le n' HPn').
        assert (Z.of_nat nmin <= Z.of_nat n') by
          (apply Nat2Z.inj_le; exact Hnmin_le).
        subst p n'. rewrite (Z2Nat.id p') in H by lia. lia.
      * destruct HnminP as [_ [HnleN _]].
        assert (p <= Zlength patn).
        { subst p.
          apply Nat2Z.inj_le in HnleN.
          unfold N in HnleN.
          rewrite (Z2Nat.id (Zlength patn)) in HnleN by (apply Zlength_nonneg).
          exact HnleN. }
        lia.
Qed.

Record critical_factorization_prop (l p : Z) : Prop := {
  cf_has_global_period :
    exists mp,
      is_minimal_period 0 patn mp /\
      0 <= l < mp /\
      0 < p <= mp /\
      min_local_period l mp
}.

Record maxsuf_prop (cmp_fn : Z -> Z -> comparison) (l p : Z) : Prop := {
  maxsuf_is_maximal : is_maximal_suffix cmp_fn patn l;
  maxsuf_period : is_minimal_period 0 (skipn' l patn) p
}.

Definition maxsuf_ret_prop (cmp_fn : Z -> Z -> comparison) (ms p : Z) : Prop :=
  maxsuf_prop cmp_fn (ms + 1) p.

Definition forward_maxsuf_prop (ms p : Z) : Prop :=
  maxsuf_ret_prop Z.compare ms p.

Definition reverse_maxsuf_prop (ms p : Z) : Prop :=
  maxsuf_ret_prop Z_compare_rev ms p.

Section MaxsufInvariant.

Context (cmp_fn : Z -> Z -> comparison).
Context (CmpFn : Cmp Z cmp_fn).

Definition maxsuf_index (i : Z) : Z := i + 1.
Definition maxsuf_probe (j : Z) : Z := j + 1.
Definition maxsuf_match_len (k : Z) : Z := k - 1.

Record maxsuf_var_range (i j k p : Z) : Prop := {
  maxsuf_range_ij : -1 <= i < j;
  maxsuf_range_kp : 1 <= k <= p;
  maxsuf_range_ijp : exists z, maxsuf_probe j = maxsuf_index i + z * p
}.

Definition maxsuf_partial_match (i j k p : Z) : Prop :=
  sublist (maxsuf_index i) (i + k) patn =
  sublist (maxsuf_probe j) (j + k) patn.

Definition maxsuf_periodicity (i j k p : Z) : Prop :=
  forall t,
    maxsuf_index i <= t ->
    t + p < j + k ->
    Znth t patn 0 = Znth (t + p) patn 0.

Definition maxsuf_optimality (i j k p : Z) : Prop :=
  forall i',
    0 <= i' < maxsuf_index i ->
    list_lex_gt Z cmp_fn (skipn' (maxsuf_index i) patn) (skipn' i' patn).

Definition maxsuf_optimality2 (i j k p : Z) : Prop :=
  forall t,
    maxsuf_index i < t < maxsuf_index i + p ->
    list_lex_gt_ex Z cmp_fn
      (sublist (maxsuf_index i) (maxsuf_index i + p) patn)
      (sublist t (maxsuf_index i + p) patn).

Record maxsuf_inv (i j k p : Z) : Prop := {
  maxsuf_inv_range : maxsuf_var_range i j k p;
  maxsuf_inv_partial : maxsuf_partial_match i j k p;
  maxsuf_inv_opt : maxsuf_optimality i j k p;
  maxsuf_inv_period : maxsuf_periodicity i j k p;
  maxsuf_inv_opt2 : maxsuf_optimality2 i j k p
}.

Definition maxsuf_inv_state (s : maxsuf_state) : Prop :=
  let '(i, j, k, p) := s in maxsuf_inv i j k p.

Lemma maxsuf_var_range_init :
  maxsuf_var_range (-1) 0 1 1.
Proof.
  constructor; simpl; try lia.
  exists 1. lia.
Qed.

Lemma maxsuf_partial_match_init :
  maxsuf_partial_match (-1) 0 1 1.
Proof.
  unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe.
  repeat rewrite Zsublist_nil; try lia.
  reflexivity.
Qed.

Lemma maxsuf_periodicity_init :
  maxsuf_periodicity (-1) 0 1 1.
Proof.
  unfold maxsuf_periodicity, maxsuf_index.
  intros; lia.
Qed.

Lemma maxsuf_periodicity_ext (i j k p t z : Z) :
  0 <= p ->
  maxsuf_periodicity i j k p ->
  maxsuf_index i <= t ->
  0 <= z ->
  t + z * p < j + k ->
  Znth t patn 0 = Znth (t + z * p) patn 0.
Proof.
  intros Hp Hper Ht Hz Hbound.
  set (n := Z.to_nat z).
  replace z with (Z.of_nat n) in * by lia.
  induction n.
  - simpl. replace (t + 0) with t by lia. reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (t + Z.succ (Z.of_nat n) * p)
      with (t + Z.of_nat n * p + p) by lia.
    pose proof Hper (t + Z.of_nat n * p) as Hstep.
    assert (maxsuf_index i <= t + Z.of_nat n * p) by lia.
    assert (t + Z.of_nat n * p + p < j + k) by lia.
    specialize (Hstep H H0).
    rewrite <- Hstep.
    apply IHn; lia.
Qed.

Lemma maxsuf_periodic_extension (i j k p z lo hi lo' hi' : Z) :
  j + k <= Zlength patn ->
  0 <= maxsuf_index i ->
  maxsuf_index i < maxsuf_probe j ->
  0 <= z ->
  0 <= p ->
  maxsuf_periodicity i j k p ->
  maxsuf_index i <= lo /\ hi <= j + k ->
  maxsuf_index i <= lo' /\ hi' <= j + k ->
  lo <= hi ->
  lo' = lo + z * p ->
  hi - lo = hi' - lo' ->
  sublist lo hi patn = sublist lo' hi' patn.
Proof.
  intros Hlen Hidx_nonneg Hij Hz Hp Hper [Hlo Hhi] [Hlo' Hhi'] Hlohi Hlo'Eq HlenEq.
  apply (list_eq_ext _ _ 0).
  split.
  - repeat rewrite Zlength_sublist; try lia.
  - intros t Ht.
    rewrite Zlength_sublist in Ht; try lia.
    repeat rewrite Znth_sublist; try lia.
    rewrite Hlo'Eq.
    replace (t + (lo + z * p)) with (t + lo + z * p) by lia.
    eapply maxsuf_periodicity_ext; eauto; try lia.
Qed.

Lemma maxsuf_optimality_init :
  maxsuf_optimality (-1) 0 1 1.
Proof.
  unfold maxsuf_optimality, maxsuf_index.
  intros; lia.
Qed.

Lemma maxsuf_optimality2_init :
  maxsuf_optimality2 (-1) 0 1 1.
Proof.
  unfold maxsuf_optimality2, maxsuf_index, maxsuf_probe.
  intros; lia.
Qed.

Lemma maxsuf_inv_init :
  maxsuf_inv (-1) 0 1 1.
Proof.
  constructor.
  - apply maxsuf_var_range_init.
  - apply maxsuf_partial_match_init.
  - apply maxsuf_optimality_init.
  - apply maxsuf_periodicity_init.
  - apply maxsuf_optimality2_init.
Qed.

Lemma maxsuf_var_range_holds (i j k p : Z) :
  maxsuf_var_range i j k p ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn (i, j, k, p);; continue_case x)
    (fun s' _ =>
      let '(i', j', k', p') := s' in maxsuf_var_range i' j' k' p').
Proof.
  intros Hrange.
  destruct Hrange as [Hij Hkp [z Hz]].
  unfold maxsuf_cal_body.
  hoare_auto; try lia.
  destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0)) eqn:Hcmp;
    hoare_auto; try lia.
  - constructor; simpl; try lia.
    exists (z + 1). unfold maxsuf_index, maxsuf_probe in *. nia.
  - constructor; simpl; try lia.
    exists z. unfold maxsuf_index, maxsuf_probe in *. nia.
  - constructor; simpl; try lia.
    exists 1. unfold maxsuf_index, maxsuf_probe in *. nia.
  - constructor; simpl; try lia.
    exists 1. unfold maxsuf_index, maxsuf_probe in *. nia.
Qed.

Lemma maxsuf_partial_match_holds (i j k p : Z) :
  maxsuf_var_range i j k p ->
  maxsuf_partial_match i j k p ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn (i, j, k, p);; continue_case x)
    (fun s' _ =>
      let '(i', j', k', p') := s' in maxsuf_partial_match i' j' k' p').
Proof.
  intros Hrange Hpm.
  destruct Hrange as [Hij Hkp [z Hz]].
  unfold maxsuf_cal_body.
  hoare_auto; try lia.
  destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0)) eqn:Hcmp;
    hoare_auto; try lia.
  - unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe.
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  - unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe in *.
    replace (i + (k + 1)) with (i + k + 1) by lia.
    replace (j + (k + 1)) with (j + k + 1) by lia.
    eapply (Zsublist_hi_plus_1 0 patn patn (i + 1) (i + k) (j + 1) (j + k)); try lia.
    + exact Hpm.
    + destruct (@cmp_Eq Z cmp_fn CmpFn _ _ Hcmp) as [Heq _].
      symmetry; exact Heq.
  - unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe.
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  - unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe.
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
Qed.

Lemma maxsuf_periodicity_holds_Eq_reset (i j k p : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Eq ->
  k = p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_periodicity i (j + p) 1 p.
Proof.
  intros Hcmp Hkp_eq Hbound Hinv.
  destruct Hinv as [Hrange _ _ Hper _].
  destruct Hrange as [Hij Hkp [z Hz]].
  unfold maxsuf_periodicity in *.
  intros t Ht Htbound.
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H as [Hlt | Heq_bound].
  - apply Hper; lia.
  - destruct (@cmp_Eq Z cmp_fn CmpFn _ _ Hcmp) as [Heq_char _].
    rewrite Heq_bound.
    rewrite Heq_char.
    assert (t = i + k + (z - 1) * p).
    { unfold maxsuf_index, maxsuf_probe in *. nia. }
    rewrite H.
    symmetry.
    eapply (maxsuf_periodicity_ext i j k p (i + k) (z - 1)); try exact Hper; try lia;
      unfold maxsuf_index, maxsuf_probe in *; nia.
Qed.

Lemma maxsuf_periodicity_holds_Eq_extend (i j k p : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Eq ->
  k <> p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_periodicity i j (k + 1) p.
Proof.
  intros Hcmp Hkp_neq Hbound Hinv.
  destruct Hinv as [Hrange _ _ Hper _].
  destruct Hrange as [Hij Hkp [z Hz]].
  unfold maxsuf_periodicity in *.
  intros t Ht Htbound.
  assert (t + p < j + k \/ t + p = j + k) by lia.
  destruct H as [Hlt | Heq_bound].
  - apply Hper; lia.
  - destruct (@cmp_Eq Z cmp_fn CmpFn _ _ Hcmp) as [Heq_char _].
    rewrite Heq_bound.
    rewrite Heq_char.
    assert (t = i + k + (z - 1) * p).
    { unfold maxsuf_index, maxsuf_probe in *. nia. }
    rewrite H.
    symmetry.
    eapply (maxsuf_periodicity_ext i j k p (i + k) (z - 1)); try exact Hper; try lia;
      unfold maxsuf_index, maxsuf_probe in *; nia.
Qed.

Lemma maxsuf_periodicity_holds_Lt (i j k p : Z) :
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_periodicity i (j + k) 1 (j + k - i).
Proof.
  intros Hbound Hinv.
  unfold maxsuf_periodicity, maxsuf_index.
  intros t Ht Htbound.
  lia.
Qed.

Lemma maxsuf_periodicity_holds_Gt (i j k p : Z) :
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_periodicity j (j + 1) 1 1.
Proof.
  intros Hbound Hinv.
  unfold maxsuf_periodicity, maxsuf_index.
  intros t Ht Htbound.
  lia.
Qed.

Lemma maxsuf_periodicity_holds (i j k p : Z) :
  maxsuf_inv i j k p ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn (i, j, k, p);; continue_case x)
    (fun s' _ =>
      let '(i', j', k', p') := s' in maxsuf_periodicity i' j' k' p').
Proof.
  intros Hinv.
  unfold maxsuf_cal_body.
  hoare_auto; try lia.
  destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0)) eqn:Hcmp;
    hoare_auto; try lia.
  - eapply maxsuf_periodicity_holds_Eq_reset; eauto.
  - eapply maxsuf_periodicity_holds_Eq_extend; eauto.
  - eapply maxsuf_periodicity_holds_Lt; eauto.
  - eapply maxsuf_periodicity_holds_Gt; eauto.
Qed.

Lemma maxsuf_optimality_holds_Eq_reset (i j k p : Z) :
  k = p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality i (j + p) 1 p.
Proof.
  intros _ _ Hinv.
  destruct Hinv as [_ _ Hopt _ _].
  exact Hopt.
Qed.

Lemma maxsuf_optimality_holds_Eq_extend (i j k p : Z) :
  k <> p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality i j (k + 1) p.
Proof.
  intros _ _ Hinv.
  destruct Hinv as [_ _ Hopt _ _].
  exact Hopt.
Qed.

Lemma maxsuf_optimality_holds_Lt (i j k p : Z) :
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality i (j + k) 1 (j + k - i).
Proof.
  intros _ Hinv.
  destruct Hinv as [_ _ Hopt _ _].
  exact Hopt.
Qed.

Lemma maxsuf_lex_gt_probe_Gt (i j k p : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Gt ->
  j + k < Zlength patn ->
  maxsuf_var_range i j k p ->
  maxsuf_partial_match i j k p ->
  list_lex_gt_ex Z cmp_fn (skipn' (maxsuf_probe j) patn) (skipn' (maxsuf_index i) patn).
Proof.
  intros Hcmp Hbound Hrange Hpm.
  destruct Hrange as [Hij Hkp [z Hz]].
  unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe in Hpm.
  apply (list_lex_gt_ex_ex' Z 0 cmp_fn (skipn' (j + 1) patn) (skipn' (i + 1) patn)).
  exists (k - 1).
  unfold list_lex_gt_ex'.
  split; [|split; [|split; [|split]]]; unfold skipn'.
  - lia.
  - rewrite Zlength_sublist; try lia.
  - rewrite Zlength_sublist; try lia.
  - repeat rewrite Zsublist_Zsublist; try (unfold maxsuf_index, maxsuf_probe in *; lia).
    replace (k - 1 + (j + 1)) with (j + k) by lia.
    replace (k - 1 + (i + 1)) with (i + k) by lia.
    symmetry; exact Hpm.
  - repeat rewrite Znth_sublist; try (unfold maxsuf_index, maxsuf_probe in *; lia).
    replace (k - 1 + (j + 1)) with (j + k) by lia.
    replace (k - 1 + (i + 1)) with (i + k) by lia.
	    exact Hcmp.
Qed.

Definition maxsuf_in_per_decomp_aux (z p r q : Z) : Prop :=
  (r = 0 /\ 0 <= q) \/
  (0 < r < p /\ 0 <= q < z) \/
  (0 < r < p /\ q = z).

Lemma maxsuf_in_per_decomp (i j k p z i' : Z) :
  maxsuf_var_range i j k p ->
  maxsuf_probe j = maxsuf_index i + z * p ->
  maxsuf_index i <= i' <= maxsuf_probe j + k - 1 ->
  exists r q,
    i' = maxsuf_index i + r + q * p /\
    maxsuf_in_per_decomp_aux z p r q.
Proof.
  intros Hrange Hz Hi'.
  destruct Hrange as [Hij Hkp _].
  set (r := (i' - maxsuf_index i) mod p).
  set (q := (i' - maxsuf_index i) / p).
  exists r, q.
  assert (0 < p) by lia.
  assert (i' - maxsuf_index i = p * q + r).
  { unfold q, r. apply Z.div_mod; lia. }
  split; [lia|].
  unfold maxsuf_in_per_decomp_aux.
  pose proof Z.mod_pos_bound (i' - maxsuf_index i) p H as Hr.
  assert (0 <= q).
  { unfold q. apply Z_div_nonneg_nonneg; lia. }
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - left; split; lia.
  - right.
    assert (0 < r < p) by lia.
    destruct (Z_lt_le_dec q z) as [Hqz | Hqz].
    + left; split; lia.
    + right; split; [lia|].
      unfold maxsuf_index, maxsuf_probe in *.
      nia.
Qed.

Lemma maxsuf_periodic_edge_Gt (i j k p i' q : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Gt ->
  j + k < Zlength patn ->
  maxsuf_var_range i j k p ->
  maxsuf_periodicity i j k p ->
  maxsuf_index i < i' < maxsuf_probe j ->
  i' = maxsuf_index i + q * p ->
  list_lex_gt_ex Z cmp_fn
    (sublist (maxsuf_probe j) (j + k + 1) patn)
    (sublist i' (i' + k) patn).
Proof.
  intros Hcmp Hbound Hrange Hper Hi' Hi'Eq.
  destruct Hrange as [Hij Hkp [z Hz]].
  assert (0 < q <= z) by (unfold maxsuf_index, maxsuf_probe in *; nia).
  apply (list_lex_gt_ex_ex' Z 0 cmp_fn
           (sublist (maxsuf_probe j) (j + k + 1) patn)
           (sublist i' (i' + k) patn)).
  exists (k - 1).
  unfold list_lex_gt_ex'.
  split; [|split; [|split; [|split]]].
  - lia.
  - rewrite Zlength_sublist; unfold maxsuf_probe in *; lia.
  - rewrite Zlength_sublist; try lia; unfold maxsuf_index, maxsuf_probe in *; lia.
  - repeat rewrite Zsublist_Zsublist; try (unfold maxsuf_index, maxsuf_probe in *; lia).
    symmetry.
    eapply (maxsuf_periodic_extension
              i j k p (z - q)
              (0 + i') (k - 1 + i')
              (0 + maxsuf_probe j) (k - 1 + maxsuf_probe j));
      try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia.
  - repeat rewrite Znth_sublist; try (unfold maxsuf_index, maxsuf_probe in *; lia).
    replace (k - 1 + maxsuf_probe j) with (j + k) by (unfold maxsuf_probe; lia).
    replace (k - 1 + i') with (i + k + q * p)
      by (unfold maxsuf_index in *; lia).
    assert (Znth (i + k) patn 0 = Znth (i + k + q * p) patn 0).
    { eapply (maxsuf_periodicity_ext i j k p (i + k) q);
        try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
    rewrite <- H0.
    exact Hcmp.
Qed.

Lemma maxsuf_optimality_holds_Gt (i j k p : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Gt ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality j (j + 1) 1 1.
Proof.
  intros Hcmp Hbound Hinv.
  unfold maxsuf_optimality.
  destruct Hinv as [Hrange Hpm Hopt Hper Hopt2].
  pose proof Hrange as Hrange'.
  destruct Hrange' as [Hij Hkp [z Hz]].
  intros i' Hi'.
  pose proof maxsuf_lex_gt_probe_Gt i j k p Hcmp Hbound Hrange Hpm as Hbase.
  assert (0 <= i' < maxsuf_index i \/ i' = maxsuf_index i \/
          maxsuf_index i < i' < maxsuf_probe j) by
    (unfold maxsuf_index, maxsuf_probe in *; lia).
  destruct H as [Hlt | [Heq | Hmid]].
  - pose proof Hopt i' Hlt as Hprev.
    eapply (list_lex_gt_trans Z 0 cmp_fn); eauto.
    unfold list_lex_gt; left; exact Hbase.
  - subst i'.
    unfold list_lex_gt; left; exact Hbase.
  - assert (exists r q,
        i' = maxsuf_index i + r + q * p /\
        maxsuf_in_per_decomp_aux z p r q).
    { eapply maxsuf_in_per_decomp; eauto.
      unfold maxsuf_index, maxsuf_probe in *; lia. }
    destruct H as [r [q [Hi'Eq Hdecomp]]].
    destruct Hdecomp as [[Hr Hq] | [[Hr Hq] | [Hr Hq]]].
    + unfold list_lex_gt; left.
      eapply (list_lex_gt_ex_plus Z cmp_fn
                (sublist (maxsuf_probe j) (j + k + 1) patn)
                (sublist i' (i' + k) patn)
                (skipn' (maxsuf_probe j) patn)
                (skipn' i' patn)); eauto.
      * apply Zsublist_is_prefix; unfold skipn', maxsuf_probe in *; lia.
      * apply Zsublist_is_prefix; unfold skipn', maxsuf_index, maxsuf_probe in *; lia.
      * eapply (maxsuf_periodic_edge_Gt i j k p i' q); eauto.
        rewrite Hi'Eq, Hr; lia.
    + specialize (Hopt2 (maxsuf_index i + r) ltac:(lia)).
      assert (list_lex_gt_ex Z cmp_fn
                (skipn' (maxsuf_index i) patn) (skipn' i' patn)).
      { eapply (list_lex_gt_ex_plus Z cmp_fn
                  (sublist (maxsuf_index i) (maxsuf_index i + p) patn)
                  (sublist (maxsuf_index i + r) (maxsuf_index i + p) patn)
                  (skipn' (maxsuf_index i) patn)
                  (skipn' i' patn)); eauto.
        - apply Zsublist_is_prefix; unfold skipn', maxsuf_index, maxsuf_probe in *; nia.
        - assert (sublist (maxsuf_index i + r) (maxsuf_index i + p) patn =
                  sublist i' (i' + p - r) patn).
          { eapply (maxsuf_periodic_extension
                      i j k p q
                      (maxsuf_index i + r) (maxsuf_index i + p)
                      i' (i' + p - r));
              try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
          rewrite H.
          apply Zsublist_is_prefix; unfold skipn', maxsuf_index, maxsuf_probe in *; nia. }
      eapply (list_lex_gt_trans Z 0 cmp_fn); eauto.
      * unfold list_lex_gt; left; exact Hbase.
      * unfold list_lex_gt; left; exact H.
    + unfold maxsuf_index, maxsuf_probe in *; nia.
Qed.

Lemma maxsuf_optimality_holds (i j k p : Z) :
  maxsuf_inv i j k p ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn (i, j, k, p);; continue_case x)
    (fun s' _ =>
      let '(i', j', k', p') := s' in maxsuf_optimality i' j' k' p').
Proof.
  intros Hinv.
  unfold maxsuf_cal_body.
  hoare_auto; try lia.
  destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0)) eqn:Hcmp;
    hoare_auto; try lia.
  - eapply maxsuf_optimality_holds_Eq_reset; eauto.
  - eapply maxsuf_optimality_holds_Eq_extend; eauto.
  - eapply maxsuf_optimality_holds_Lt; eauto.
  - eapply maxsuf_optimality_holds_Gt; eauto.
Qed.

Lemma maxsuf_optimality2_holds_Eq_reset (i j k p : Z) :
  k = p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality2 i (j + p) 1 p.
Proof.
  intros _ _ Hinv.
  destruct Hinv as [_ _ _ _ Hopt2].
  exact Hopt2.
Qed.

Lemma maxsuf_optimality2_holds_Eq_extend (i j k p : Z) :
  k <> p ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality2 i j (k + 1) p.
Proof.
  intros _ _ Hinv.
  destruct Hinv as [_ _ _ _ Hopt2].
  exact Hopt2.
Qed.

Lemma maxsuf_optimality2_holds_Lt (i j k p : Z) :
  cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) = Lt ->
  j + k < Zlength patn ->
  maxsuf_inv i j k p ->
  maxsuf_optimality2 i (j + k) 1 (j + k - i).
Proof.
  intros Hcmp Hbound Hinv.
  destruct Hinv as [Hrange Hpm Hopt Hper Hopt2].
  pose proof Hrange as Hrange'.
  destruct Hrange' as [Hij Hkp [z Hz]].
  unfold maxsuf_optimality2.
  intros t Ht.
  assert (exists r q,
      t = maxsuf_index i + r + q * p /\
      maxsuf_in_per_decomp_aux z p r q).
  { eapply maxsuf_in_per_decomp; eauto.
    unfold maxsuf_index, maxsuf_probe in *; lia. }
  destruct H as [r [q [HtEq Hdecomp]]].
  destruct Hdecomp as [[Hr Hq] | [[Hr Hq] | [Hr Hq]]];
    replace (maxsuf_index i + (j + k - i)) with (j + k + 1) by
      (unfold maxsuf_index; lia).
  - assert (0 < q <= z) by (unfold maxsuf_index, maxsuf_probe in *; nia).
    set (l1 := sublist (maxsuf_index i) (j + k + 1) patn).
    set (l2 := sublist t (j + k + 1) patn).
    set (l1' := sublist (maxsuf_index i) (maxsuf_index i + (j + k + 1 - t)) patn).
    assert (list_lex_gt_ex Z cmp_fn l1' l2).
    { apply (list_lex_gt_ex_ex' Z 0 cmp_fn l1' l2).
      exists (j + k - t).
      unfold list_lex_gt_ex'.
      split; [|split; [|split; [|split]]]; unfold l1', l2.
      + unfold maxsuf_index in *; lia.
      + rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; lia.
      + rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; lia.
      + repeat rewrite Zsublist_Zsublist;
          try (unfold maxsuf_index, maxsuf_probe in *; lia).
        eapply (maxsuf_periodic_extension
                  i j k p q
                  (0 + maxsuf_index i) (j + k - t + maxsuf_index i)
                  (0 + t) (j + k - t + t));
          try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia.
      + repeat rewrite Znth_sublist;
          try (unfold maxsuf_index, maxsuf_probe in *; lia).
        replace (j + k - t + t) with (j + k) by lia.
        assert (Znth (i + k) patn 0 =
                Znth (j + k - t + maxsuf_index i) patn 0).
        { replace (j + k - t + maxsuf_index i) with (i + k + (z - q) * p)
            by (unfold maxsuf_index, maxsuf_probe in *; nia).
          eapply (maxsuf_periodicity_ext i j k p (i + k) (z - q));
            try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
        rewrite <- H0.
        apply (@cmp_Lt_Gt Z cmp_fn CmpFn).
        exact Hcmp. }
    eapply (list_lex_gt_ex_trans' Z 0 cmp_fn); eauto.
    unfold list_lex_gt; right.
    unfold is_proper_prefix.
    split.
    + unfold l1, l1'. apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; lia.
    + unfold l1, l1'. repeat rewrite Zlength_sublist;
        unfold maxsuf_index, maxsuf_probe in *; lia.
  - set (l1 := sublist (maxsuf_index i) (maxsuf_index i + p) patn).
    set (l2 := sublist t (t + p - r) patn).
    assert (list_lex_gt_ex Z cmp_fn l1 l2).
    { replace l2 with (sublist (maxsuf_index i + r) (maxsuf_index i + p) patn).
      - apply (Hopt2 (maxsuf_index i + r)); lia.
      - unfold l2.
        eapply (maxsuf_periodic_extension
                  i j k p q
                  (maxsuf_index i + r) (maxsuf_index i + p)
                  t (t + p - r));
          try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
    eapply (list_lex_gt_ex_plus Z cmp_fn l1 l2
              (sublist (maxsuf_index i) (j + k + 1) patn)
              (sublist t (j + k + 1) patn)); eauto.
    + unfold l1. apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; nia.
    + unfold l2. apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; nia.
  - assert (1 <= z) by (unfold maxsuf_index, maxsuf_probe in *; nia).
    set (l1 := sublist (maxsuf_index i) (j + k + 1) patn).
    set (l1' := sublist (maxsuf_index i) (maxsuf_index i + p) patn).
    set (l2 := sublist (maxsuf_index i + r) (maxsuf_index i + p) patn).
    set (l2' := sublist (maxsuf_index i + r)
                         (maxsuf_index i + r + (j + k + 1 - t)) patn).
    set (l3 := sublist t (j + k + 1) patn).
    assert (list_lex_gt Z cmp_fn l1 l1').
    { unfold list_lex_gt; right.
      unfold is_proper_prefix.
      split.
      - unfold l1, l1'.
        eapply (Zsublist_is_prefix patn
                  (maxsuf_index i) (maxsuf_index i + p) (j + k + 1));
          unfold maxsuf_index, maxsuf_probe in *; nia.
      - unfold l1, l1'. repeat rewrite Zlength_sublist;
          unfold maxsuf_index, maxsuf_probe in *; nia. }
    assert (list_lex_gt_ex Z cmp_fn l1' l2).
    { apply (Hopt2 (maxsuf_index i + r)); lia. }
    assert (list_lex_ge Z cmp_fn l2 l2').
    { assert (Hkp_cases : k = p \/ k <> p) by lia.
      destruct Hkp_cases as [Hkp_eq | Hkp_neq].
      - unfold list_lex_ge; right; unfold l2, l2'.
        replace (maxsuf_index i + r + (j + k + 1 - t))
          with (maxsuf_index i + p) by
          (unfold maxsuf_index, maxsuf_probe in *; nia).
        reflexivity.
      - unfold list_lex_ge; left; unfold l2, l2'.
        unfold list_lex_gt; right.
        unfold is_proper_prefix.
        split.
        + apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; nia.
        + repeat rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; nia. }
    assert (list_lex_gt_ex Z cmp_fn l2' l3).
    { apply (list_lex_gt_ex_ex' Z 0 cmp_fn l2' l3).
      exists (j + k - t).
      unfold list_lex_gt_ex'.
      split; [|split; [|split; [|split]]]; unfold l2', l3.
      + unfold maxsuf_index in *; lia.
      + rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; nia.
      + rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; nia.
      + repeat rewrite Zsublist_Zsublist;
          try (unfold maxsuf_index, maxsuf_probe in *; nia).
        eapply (maxsuf_periodic_extension
                  i j k p z
                  (0 + (maxsuf_index i + r)) (j + k - t + (maxsuf_index i + r))
                  (0 + t) (j + k - t + t));
          try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia.
      + repeat rewrite Znth_sublist;
          try (unfold maxsuf_index, maxsuf_probe in *; nia).
        replace (j + k - t + (maxsuf_index i + r)) with (i + k)
          by (unfold maxsuf_index, maxsuf_probe in *; nia).
        replace (j + k - t + t) with (j + k) by lia.
        apply (@cmp_Lt_Gt Z cmp_fn CmpFn).
        exact Hcmp. }
    destruct H2 as [Hge | Heq].
    + eapply (list_lex_gt_ex_trans' Z 0 cmp_fn); eauto.
      eapply (list_lex_gt_ex_trans Z 0 cmp_fn); eauto.
      eapply (list_lex_gt_ex_trans' Z 0 cmp_fn); eauto.
    + eapply (list_lex_gt_ex_trans' Z 0 cmp_fn); eauto.
      eapply (list_lex_gt_ex_trans Z 0 cmp_fn); eauto.
      rewrite Heq; exact H3.
Qed.

Lemma maxsuf_optimality2_holds_Gt (j : Z) :
  maxsuf_optimality2 j (j + 1) 1 1.
Proof.
  unfold maxsuf_optimality2.
  intros; lia.
Qed.

Lemma maxsuf_optimality2_holds (i j k p : Z) :
  maxsuf_inv i j k p ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn (i, j, k, p);; continue_case x)
    (fun s' _ =>
      let '(i', j', k', p') := s' in maxsuf_optimality2 i' j' k' p').
Proof.
  intros Hinv.
  unfold maxsuf_cal_body.
  hoare_auto; try lia.
  destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0)) eqn:Hcmp;
    hoare_auto; try lia.
  - eapply maxsuf_optimality2_holds_Eq_reset; eauto.
  - eapply maxsuf_optimality2_holds_Eq_extend; eauto.
  - eapply maxsuf_optimality2_holds_Lt; eauto.
  - apply maxsuf_optimality2_holds_Gt.
Qed.

Lemma maxsuf_inv_holds (s : maxsuf_state) :
  maxsuf_inv_state s ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn s;; continue_case x)
    (fun s' _ => maxsuf_inv_state s').
Proof.
  unfold maxsuf_inv_state.
  intros Hinv.
  destruct s as [[[i j] k] p].
  simpl in Hinv.
  destruct Hinv as [Hrange0 Hpm0 Hopt0 Hper0 Hopt20].
  assert (Hinv0 : maxsuf_inv i j k p) by (constructor; auto).
  pose proof (maxsuf_var_range_holds i j k p Hrange0) as HrangeH.
  pose proof (maxsuf_partial_match_holds i j k p Hrange0 Hpm0) as HpmH.
  pose proof (maxsuf_optimality_holds i j k p Hinv0) as HoptH.
  pose proof (maxsuf_periodicity_holds i j k p Hinv0) as HperH.
  pose proof (maxsuf_optimality2_holds i j k p Hinv0) as Hopt2H.
  unfold Hoare in *.
  destruct HrangeH as [HrangeN HrangeE].
  destruct HpmH as [HpmN HpmE].
  destruct HoptH as [HoptN HoptE].
  destruct HperH as [HperN HperE].
  destruct Hopt2H as [Hopt2N Hopt2E].
  split.
  - intros s' st1 st2 _ Hnrm.
    destruct s' as [[[i' j'] k'] p']; simpl.
    constructor.
    + exact (HrangeN (i', j', k', p') st1 st2 I Hnrm).
    + exact (HpmN (i', j', k', p') st1 st2 I Hnrm).
    + exact (HoptN (i', j', k', p') st1 st2 I Hnrm).
    + exact (HperN (i', j', k', p') st1 st2 I Hnrm).
    + exact (Hopt2N (i', j', k', p') st1 st2 I Hnrm).
  - intros st _ Herr.
    eapply HrangeE; eauto.
Qed.

Lemma maxsuf_break_is_maximal_suffix (s : maxsuf_state) :
  maxsuf_inv_state s ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn s;; break_case x)
    (fun res _ => is_maximal_suffix cmp_fn patn (fst res + 1)).
Proof.
  unfold maxsuf_inv_state.
  intros Hinv.
  destruct s as [[[i j] k] p].
  simpl in Hinv.
  destruct Hinv as [Hrange Hpm Hopt Hper Hopt2].
  pose proof Hrange as Hrange'.
  destruct Hrange' as [Hij Hkp [z Hz]].
  assert (Hz_pos : 1 <= z) by (unfold maxsuf_index, maxsuf_probe in *; nia).
  unfold maxsuf_cal_body.
  hoare_auto; simpl.
  unfold is_maximal_suffix.
  split.
  - lia.
  - intros pos Hpos.
    destruct (Z.lt_trichotomy pos (maxsuf_index i)) as [Hlt | [Heq | Hgt]].
    + unfold list_lex_ge.
      left.
      apply Hopt; lia.
    + rewrite Heq.
      unfold list_lex_ge.
      right.
      reflexivity.
    + assert (pos < j + k \/ j + k <= pos) as [Hinside | Hnil] by lia.
      * unfold list_lex_ge, skipn'.
        left.
        assert (Hdecomp_exists : exists r q,
            pos = maxsuf_index i + r + q * p /\
            maxsuf_in_per_decomp_aux z p r q).
        { eapply maxsuf_in_per_decomp; eauto.
          unfold maxsuf_index, maxsuf_probe in *; lia. }
        destruct Hdecomp_exists as [r [q [HposEq Hdecomp]]].
        destruct Hdecomp as [[Hr Hq] | [[Hr Hq] | [Hr Hq]]].
        -- unfold list_lex_gt; right.
           unfold is_proper_prefix.
           split.
           ++ assert (Hpref_eq :
                      sublist (maxsuf_index i) (maxsuf_index i + Zlength patn - pos) patn =
                      sublist pos (Zlength patn) patn).
              { eapply (maxsuf_periodic_extension
                          i j k p q
                          (maxsuf_index i) (maxsuf_index i + Zlength patn - pos)
                          pos (Zlength patn));
	                  try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
	              unfold skipn'.
              rewrite <- Hpref_eq.
	              apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; lia.
           ++ repeat rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; lia.
        -- unfold list_lex_gt; left.
           pose proof (Hopt2 (maxsuf_index i + r) ltac:(lia)) as Hopt2r.
           eapply (list_lex_gt_ex_plus Z cmp_fn
                     (sublist (maxsuf_index i) (maxsuf_index i + p) patn)
                     (sublist (maxsuf_index i + r) (maxsuf_index i + p) patn)
                     (skipn' (maxsuf_index i) patn)
                     (skipn' pos patn)); eauto.
           ++ apply Zsublist_is_prefix; unfold skipn', maxsuf_index, maxsuf_probe in *; nia.
           ++ assert (Hpref_eq :
                      sublist (maxsuf_index i + r)
                        (maxsuf_index i + r + Zlength patn - pos) patn =
                      sublist pos (Zlength patn) patn).
              { eapply (maxsuf_periodic_extension
                          i j k p q
                          (maxsuf_index i + r)
                          (maxsuf_index i + r + Zlength patn - pos)
                          pos (Zlength patn));
                  try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
              unfold skipn'.
              rewrite <- Hpref_eq.
	              apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; nia.
        -- set (l1 := sublist (maxsuf_index i) (Zlength patn) patn).
           set (l1' := sublist (maxsuf_index i) (maxsuf_index i + p) patn).
           set (l2 := sublist (maxsuf_index i + r) (maxsuf_index i + p) patn).
           set (l2' := sublist (maxsuf_index i + r)
                              (maxsuf_index i + r + Zlength patn - pos) patn).
           set (l3 := sublist pos (Zlength patn) patn).
           assert (H_l1_l1' : list_lex_gt Z cmp_fn l1 l1').
           { unfold list_lex_gt; right.
             unfold is_proper_prefix.
             split.
             - unfold l1, l1'. apply Zsublist_is_prefix;
                 unfold maxsuf_index, maxsuf_probe in *; nia.
             - unfold l1, l1'. repeat rewrite Zlength_sublist;
                 unfold maxsuf_index, maxsuf_probe in *; nia. }
           assert (H_l1'_l2 : list_lex_gt Z cmp_fn l1' l2).
           { unfold list_lex_gt; left.
             apply (Hopt2 (maxsuf_index i + r)); lia. }
           assert (H_l2_l2' : list_lex_gt Z cmp_fn l2 l2').
           { unfold list_lex_gt; right.
             unfold is_proper_prefix.
             split.
             - unfold l2, l2'. apply Zsublist_is_prefix;
                 unfold maxsuf_index, maxsuf_probe in *; nia.
             - unfold l2, l2'. repeat rewrite Zlength_sublist;
                 unfold maxsuf_index, maxsuf_probe in *; nia. }
           assert (Hl2'_l3 : l2' = l3).
           { unfold l2', l3.
             eapply (maxsuf_periodic_extension
                       i j k p q
                       (maxsuf_index i + r)
                       (maxsuf_index i + r + Zlength patn - pos)
                       pos (Zlength patn));
               try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia. }
           eapply (list_lex_gt_trans Z 0 cmp_fn CmpFn l1 l1' l3).
           ++ exact H_l1_l1'.
           ++ eapply (list_lex_gt_trans Z 0 cmp_fn CmpFn l1' l2 l3).
              ** exact H_l1'_l2.
              ** rewrite <- Hl2'_l3.
                 exact H_l2_l2'.
      * unfold skipn'.
        rewrite (Zsublist_nil patn pos (Zlength patn)); try lia.
        apply list_lex_ge_nil.
  all: try solve [unfold skipn', maxsuf_index, maxsuf_probe in *; nia | auto].
  - unfold break_case.
    destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0));
      hoare_auto;
      unfold Hoare; split; intros; simpl in *; tauto.
Qed.

Lemma maxsuf_cal_is_maximal_suffix (init : maxsuf_state) :
  maxsuf_inv_state init ->
  Hoare
    (fun _ => True)
    (maxsuf_cal cmp_fn patn init)
    (fun res _ => is_maximal_suffix cmp_fn patn (fst res + 1)).
Proof.
  intros Hinit.
  unfold maxsuf_cal.
  eapply Hoare_conseq with (P2 := fun _ => maxsuf_inv_state init).
  2:{
    intros res st Hres.
    exact Hres.
  }
  2:{
    eapply (@Hoare_repeat_break'
              unit maxsuf_state maxsuf_ret
              (maxsuf_cal_body cmp_fn patn)
              (fun s _ => maxsuf_inv_state s)
              (fun res _ => is_maximal_suffix cmp_fn patn (fst res + 1))).
    - intros s. unfold Hoare. split.
      + intros a st1 st2 Hs Hnrm.
        pose proof (maxsuf_inv_holds s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [HN _].
        eapply HN; eauto.
      + intros st Hs Herr.
        pose proof (maxsuf_inv_holds s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [_ HE].
        eapply HE; eauto.
    - intros s. unfold Hoare. split.
      + intros a st1 st2 Hs Hnrm.
        pose proof (maxsuf_break_is_maximal_suffix s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [HN _].
        eapply HN; eauto.
      + intros st Hs Herr.
        pose proof (maxsuf_break_is_maximal_suffix s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [_ HE].
        eapply HE; eauto.
  }
  intros st _.
  exact Hinit.
Qed.

Lemma maxsuf_break_min_period (s : maxsuf_state) :
  maxsuf_inv_state s ->
  Hoare
    (fun _ => True)
    (x <- maxsuf_cal_body cmp_fn patn s;; break_case x)
    (fun res _ => is_minimal_period 0 (skipn' (fst res + 1) patn) (snd res)).
Proof.
  unfold maxsuf_inv_state.
  intros Hinv.
  destruct s as [[[i j] k] p].
  simpl in Hinv.
  destruct Hinv as [Hrange Hpm Hopt Hper Hopt2].
  pose proof Hrange as Hrange'.
  destruct Hrange' as [Hij Hkp [z Hz]].
  assert (Hz_pos : 1 <= z) by (unfold maxsuf_index, maxsuf_probe in *; nia).
  unfold maxsuf_cal_body.
  hoare_auto; simpl.
  - unfold is_minimal_period.
    split.
    + unfold is_period, skipn'.
      split; [lia|].
      intros t Ht Htbound.
      rewrite Zlength_sublist in Htbound; try lia.
      repeat rewrite Znth_sublist; try lia.
      replace (t + (i + 1)) with (maxsuf_index i + t) by (unfold maxsuf_index; lia).
      replace (t + p + (i + 1)) with (maxsuf_index i + t + 1 * p)
        by (unfold maxsuf_index; lia).
      eapply (maxsuf_periodicity_ext i j k p (maxsuf_index i + t) 1);
        try exact Hper; unfold maxsuf_index, maxsuf_probe in *; nia.
    + intros p' Hp'.
      destruct (Z_lt_ge_dec p' p) as [Hp'lt | Hp'ge]; [|lia].
      unfold is_period, skipn' in Hp'.
      rewrite Zlength_sublist in Hp'; try lia.
      destruct Hp' as [Hp'pos Hp'per].
      assert (Hper' : maxsuf_periodicity i j k p').
      { unfold maxsuf_periodicity.
        intros t Ht Htbound.
        specialize (Hp'per (t - maxsuf_index i)).
        rewrite Znth_sublist in Hp'per; try (unfold maxsuf_index, maxsuf_probe in *; lia).
        rewrite Znth_sublist in Hp'per; try (unfold maxsuf_index, maxsuf_probe in *; lia).
        replace (t - maxsuf_index i + (i + 1)) with t in Hp'per
          by (unfold maxsuf_index in *; lia).
        replace (t - maxsuf_index i + p' + (i + 1)) with (t + p') in Hp'per
          by (unfold maxsuf_index in *; lia).
        apply Hp'per; unfold maxsuf_index, maxsuf_probe in *; lia. }
      assert (Hseg :
        sublist (maxsuf_index i) (maxsuf_index i + p - p') patn =
        sublist (maxsuf_index i + p') (maxsuf_index i + p) patn).
      { eapply (maxsuf_periodic_extension
                  i j k p' 1
                  (maxsuf_index i) (maxsuf_index i + p - p')
                  (maxsuf_index i + p') (maxsuf_index i + p));
          try exact Hper'; unfold maxsuf_index, maxsuf_probe in *; nia. }
      specialize (Hopt2 (maxsuf_index i + p') ltac:(lia)).
      assert (Hprefix :
        is_proper_prefix Z
          (sublist (maxsuf_index i + p') (maxsuf_index i + p) patn)
          (sublist (maxsuf_index i) (maxsuf_index i + p) patn)).
      { unfold is_proper_prefix.
        split.
        - rewrite <- Hseg.
          apply Zsublist_is_prefix; unfold maxsuf_index, maxsuf_probe in *; nia.
        - repeat rewrite Zlength_sublist; unfold maxsuf_index, maxsuf_probe in *; nia. }
      pose proof (proper_prefix_discriminate_gt_ex Z cmp_fn _ _ CmpFn Hopt2 Hprefix).
      tauto.
  - unfold break_case.
    destruct (cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0));
      hoare_auto;
      unfold Hoare; split; intros; simpl in *; tauto.
Qed.

Lemma maxsuf_cal_min_period (init : maxsuf_state) :
  maxsuf_inv_state init ->
  Hoare
    (fun _ => True)
    (maxsuf_cal cmp_fn patn init)
    (fun res _ => is_minimal_period 0 (skipn' (fst res + 1) patn) (snd res)).
Proof.
  intros Hinit.
  unfold maxsuf_cal.
  eapply Hoare_conseq with (P2 := fun _ => maxsuf_inv_state init).
  2:{
    intros res st Hres.
    exact Hres.
  }
  2:{
    eapply (@Hoare_repeat_break'
              unit maxsuf_state maxsuf_ret
              (maxsuf_cal_body cmp_fn patn)
              (fun s _ => maxsuf_inv_state s)
              (fun res _ => is_minimal_period 0 (skipn' (fst res + 1) patn) (snd res))).
    - intros s. unfold Hoare. split.
      + intros a st1 st2 Hs Hnrm.
        pose proof (maxsuf_inv_holds s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [HN _].
        eapply HN; eauto.
      + intros st Hs Herr.
        pose proof (maxsuf_inv_holds s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [_ HE].
        eapply HE; eauto.
    - intros s. unfold Hoare. split.
      + intros a st1 st2 Hs Hnrm.
        pose proof (maxsuf_break_min_period s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [HN _].
        eapply HN; eauto.
      + intros st Hs Herr.
        pose proof (maxsuf_break_min_period s Hs) as HH.
        unfold Hoare in HH.
        destruct HH as [_ HE].
        eapply HE; eauto.
  }
  intros st _.
  exact Hinit.
Qed.

Lemma maxsuf_cal_sound (init : maxsuf_state) :
  maxsuf_inv_state init ->
  Hoare
    (fun _ => True)
    (maxsuf_cal cmp_fn patn init)
    (fun res _ => maxsuf_prop cmp_fn (fst res + 1) (snd res)).
Proof.
  intros Hinit.
  eapply Hoare_conseq
    with
      (P2 := fun _ => True)
      (Q2 := fun res _ =>
               is_maximal_suffix cmp_fn patn (fst res + 1) /\
               is_minimal_period 0 (skipn' (fst res + 1) patn) (snd res)).
  2:{
    intros [ms p] st [Hmax Hper].
    constructor; simpl in *; auto.
  }
  2:{
    apply Hoare_conj.
    - apply maxsuf_cal_is_maximal_suffix; exact Hinit.
    - apply maxsuf_cal_min_period; exact Hinit.
  }
  intros st _; exact I.
Qed.

End MaxsufInvariant.

Theorem maxsuf_fwd_sound :
  Hoare
    (fun _ => True)
    (maxsuf_fwd patn)
    (fun res _ => forward_maxsuf_prop (fst res) (snd res)).
Proof.
  unfold maxsuf_fwd, forward_maxsuf_prop, maxsuf_ret_prop.
  pose proof (maxsuf_cal_sound Z.compare Cmp_Zcompare (-1, 0, 1, 1)) as Hsound.
  apply Hsound.
  exact (maxsuf_inv_init Z.compare).
Qed.

Theorem maxsuf_rev_sound :
  Hoare
    (fun _ => True)
    (maxsuf_rev patn)
    (fun res _ => reverse_maxsuf_prop (fst res) (snd res)).
Proof.
  unfold maxsuf_rev, reverse_maxsuf_prop, maxsuf_ret_prop.
  change (fun a b : Z => Z.compare b a) with Z_compare_rev.
  pose proof (maxsuf_cal_sound Z_compare_rev Cmp_Zcompare_rev (-1, 0, 1, 1)) as Hsound.
  apply Hsound.
  exact (maxsuf_inv_init Z_compare_rev).
Qed.

Lemma maxsuffix_cut_no_full_local_period
    (cmp_fn : Z -> Z -> comparison) (i : Z) (w : list Z) :
  Cmp Z cmp_fn ->
  is_maximal_suffix cmp_fn patn i ->
  is_suffix w (sublist 0 i patn) ->
  is_prefix w (sublist i (Zlength patn) patn) ->
  w = nil.
Proof.
  intros CmpFn Hmax Hsuffix Hprefix.
  destruct Hmax as [Hirange Hmax].
  assert (Hsuf_range : 0 <= 0 <= i /\ i <= Zlength patn) by lia.
  pose proof Zsublist_suffix_range _ _ _ patn Hsuf_range Hsuffix as Hw_len1.
  assert (Hpref_range : 0 <= i <= Zlength patn /\ Zlength patn <= Zlength patn) by lia.
  pose proof Zsublist_prefix_range _ _ _ patn Hpref_range Hprefix as Hw_len2.
  pose proof Zlength_nonneg w as Hw_nonneg.
  pose proof Hmax (i - Zlength w) ltac:(lia) as Hleft.
  pose proof Hmax (i + Zlength w) ltac:(lia) as Hright.
  assert (Hw_left : w = sublist (i - Zlength w) i patn).
  { eapply Zsublist_suffix_inv; eauto; lia. }
  assert (Hw_right : w = sublist i (i + Zlength w) patn).
  { eapply Zsublist_prefix_inv; eauto; lia. }
  unfold skipn' in Hleft, Hright.
  set (t := sublist (i + Zlength w) (Zlength patn) patn) in *.
  assert (Hv_decomp : sublist i (Zlength patn) patn = w ++ t).
  { rewrite Hw_right. subst t.
    rewrite (sublist_split i (Zlength patn) (i + Zlength w)); try lia.
    reflexivity. }
  rewrite Hv_decomp in Hleft, Hright.
  assert (Hleft_decomp :
    sublist (i - Zlength w) (Zlength patn) patn = w ++ w ++ t).
  { rewrite (sublist_split (i - Zlength w) (Zlength patn) i); try lia.
    rewrite <- Hw_left. rewrite Hv_decomp. reflexivity. }
  rewrite Hleft_decomp in Hleft.
  apply (list_lex_ge_param_prefix_inv Z 0 cmp_fn t (w ++ t) w CmpFn) in Hleft.
  pose proof list_lex_ge_param_assym Z 0 cmp_fn t (w ++ t) CmpFn Hleft Hright as Hwt.
  apply (f_equal (fun xs => Zlength xs)) in Hwt.
  rewrite Zlength_app in Hwt.
  assert (Zlength w = 0) by lia.
  apply Zlength_zero_iff_nil; auto.
Qed.

Lemma maxsuffix_cut_u_not_nil (i j p : Z) :
  is_maximal_suffix Z.compare patn i ->
  is_maximal_suffix Z_compare_rev patn j ->
  is_minimal_period 0 patn p ->
  1 < p ->
  j <= i ->
  0 < i.
Proof.
  intros Hmax Hmax_rev Hmp Hp_gt Hji.
  destruct Hmax as [Hirange Hmax].
  destruct Hmax_rev as [Hjrange Hmax_rev].
  destruct Hmp as [Hper Hmin].
  destruct Hper as [Hp_pos Hper].
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0]; [|lia].
  subst i.
  assert (j = 0) by lia.
  subst j.
  assert (Hskip0 : skipn' 0 patn = patn).
  { unfold skipn'. apply Zsublist_all. }
  assert (Hlen : 1 <= Zlength patn).
  { pose proof Zlength_nonneg patn.
    destruct (Z.eq_dec (Zlength patn) 0) as [Hz | Hz]; [|lia].
    apply Zlength_nil_inv in Hz; contradiction. }
  specialize (Hmax 1 ltac:(lia)).
  specialize (Hmax_rev 1 ltac:(lia)).
  rewrite Hskip0 in Hmax, Hmax_rev.
  set (y := skipn' 1 patn) in *.
  assert (Hy_pref : is_prefix y patn).
  { apply (prefix_ordering Z 0 Z.compare Cmp_Zcompare patn y); auto.
    apply list_lex_ge_Z_compare_rev_as_cmp_rev.
    exact Hmax_rev. }
  assert (Hy_suf : is_suffix y patn).
  { exists (sublist 0 1 patn).
    subst y. unfold skipn'.
    rewrite <- Zsublist_all at 1.
    rewrite (sublist_split 0 (Zlength patn) 1) at 1; try lia.
    reflexivity. }
  assert (Hperiod1 : is_period 0 patn 1).
  { apply (max_border_min_period_spec_1 0 _ _ Hy_pref Hy_suf).
    subst y. unfold skipn'. rewrite Zlength_sublist; try lia. }
  specialize (Hmin 1 Hperiod1).
  lia.
Qed.

Theorem critical_factorization_theorem:
  forall i j p,
    is_maximal_suffix Z.compare patn i -> 
    is_maximal_suffix Z_compare_rev patn j ->
    is_minimal_period 0 patn p -> (* Assume the global period is known *)
    min_local_period (Z.max i j) p.
Proof.
  intros.
  destruct H. destruct H0.
  destruct H1. destruct H1.
  assert (p = 1 \/ 1 < p) by lia.
  destruct H6.
  1:{ (* Trivial case: p = 1 *) 
      subst p. unfold min_local_period.
      split.
      - unfold local_period.
        split; [lia|split;[lia|]]. intros t. intros.
        pose proof H5 (Z.max i j + t - 1) ltac:(lia) ltac:(lia).
        replace (Z.max i j + t - 1 + 1) with (Z.max i j + t) in H9 by lia.
        apply H9.
      - intros.
        unfold local_period in H6.
        lia. }
  (* Case 1 < p *)
  set (u := sublist 0 i patn).
  set (v := sublist i (Zlength patn) patn).
  set (u' := sublist 0 j patn).
  set (v' := sublist j (Zlength patn) patn).
  assert (j <= i \/ i < j) by lia.
  destruct H7.
  - (* First discuss the case i ≥ j (forward larger); overall symmetric *)
    replace (Z.max i j) with i by lia.
    assert (0 < i). (* First, derive u ≠ ε *)
    { apply (maxsuffix_cut_u_not_nil i j p); try auto.
      - split; try auto. (* These have been unpacked earlier in the proofs *)
      - split; try auto.
      - split; try auto. split; try auto. }
    pose proof min_local_period_existence i ltac:(lia).
    destruct H9 as [r [? [? ?]]].
    destruct H10 as [? [? ?]].
    assert (r > i).
    { assert (r <= i \/ r > i) by lia.
      assert (r <= Zlength patn - i \/ r > Zlength patn - i) by lia.
      destruct H14; [|auto]; destruct H15.
      - set (w:= sublist i (i + r) patn).
        assert (w = sublist (i - r) i patn).
        { subst w.
          apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t ?. rewrite Zlength_sublist in H16; try lia.
            repeat rewrite Znth_sublist; try lia.
            replace (t + i) with (i + t) by lia.
            replace (t + (i - r)) with (i + t - r) by lia.
            symmetry. apply (H13 t); try lia. }
        assert (is_prefix w (sublist i (Zlength patn) patn)).
        { subst w.
          apply Zsublist_is_prefix; try lia. }
        assert (is_suffix w (sublist 0 i patn)).
        { rewrite H16.
          apply Zsublist_is_suffix; try lia. }
        assert (w = nil).
        { apply (maxsuffix_cut_no_full_local_period Z.compare i w _); try auto.
          split; auto. }
        assert (Zlength w = r).
        { apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_sublist in H16; try lia. }
        rewrite H19 in H20. rewrite Zlength_nil in H20.
        lia. (* Contradiction: r > 0 vs r = 0 from w = nil *)
      - (* Use properties related to maximal_suffix *)
        pose proof H2 (i - r) ltac:(lia).
        assert (sublist (i - r) (Zlength patn - r) patn 
              = sublist i (Zlength patn) patn).
        { apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t Htrange.
            rewrite Zlength_sublist in Htrange; try lia.
            repeat rewrite Znth_sublist; try lia.
            specialize (H13 t ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (t + (i - r)) with (i + t - r) by lia.
            replace (t + i) with (i + t) by lia.
            apply H13.
        }
        destruct H16; [destruct H16|].
        + assert (is_proper_prefix Z (skipn' i patn) (skipn' (i - r) patn)).
          { unfold is_proper_prefix.
            split; unfold skipn'.
            - exists (sublist (Zlength patn - r) (Zlength patn) patn).
              rewrite <- H17.
              rewrite <- sublist_split; try lia.
              reflexivity.
            - repeat rewrite Zlength_sublist; try lia.
          }
          pose proof (proper_prefix_discriminate_gt_ex' Z Z.compare _ _ Cmp_Zcompare H16 H18).
          tauto.
        + unfold is_proper_prefix in H16.
          unfold skipn' in H16.
          destruct H16 as [[s ?] ?].
          apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_sublist in H16; try lia.
          rewrite Zlength_app in H16.
          rewrite Zlength_sublist in H16; try lia.
          assert (0 <= Zlength s). { apply Zlength_nonneg. }
          lia. (* Length contradiction *)
        + apply (f_equal (fun l => Zlength l)) in H16.
          unfold skipn' in H16.
          rewrite Zlength_sublist in H16; try lia.
          rewrite Zlength_sublist in H16; try lia.
      }
    (* First formalize z *) 
    set (z := sublist 0 (r - Zlength u) v).
    assert (r = Zlength (z ++ u)).
    { rewrite Zlength_app. subst z. subst u.
      repeat rewrite Zlength_sublist; try lia.
      split; try lia. subst v.
      rewrite Zlength_sublist; try lia. }
    (* Continue with two cases: r > |v| or r <= |v| *)
    assert (r > Zlength patn - i \/ r <= Zlength patn - i) by lia.
    destruct H16.
    + (* r > |v| *)
      assert (is_prefix v (z ++ u)).
      { unfold is_prefix.
        exists (sublist (Zlength u + Zlength v - r) (Zlength u) u).
        subst z. subst u. subst v.
        repeat rewrite Zlength_sublist; try lia.
        repeat rewrite Zsublist_Zsublist; try lia.
        simpl. replace (r - (i - 0) + i) with r by lia.
        replace (i - 0 + (Zlength patn - i) - r + 0) with (Zlength patn - r) by lia.
        replace (i - 0 + 0) with i by lia.
        rewrite (sublist_split i (Zlength patn) r); try lia.
        rewrite <- app_assoc.
        assert (sublist 0 i patn = sublist r (Zlength patn) patn
                                 ++ sublist (Zlength patn - r) i patn).
        { apply (Zsublist_eq_ext 0).
          - rewrite Zlength_app.
            repeat rewrite Zlength_sublist; try lia.
          - intros t ?.
            rewrite Zlength_sublist in H17; try lia.
            assert (t < Zlength patn - r \/ Zlength patn - r <= t) by lia.
            destruct H18.
            + rewrite app_Znth1.
              2:{ rewrite Zlength_sublist; try lia. }
              repeat rewrite Znth_sublist; try lia.
              replace (t + 0) with t by lia.
              specialize (H13 (t + r - i)).
              replace (i + (t + r - i) - r) with t in H13 by lia.
              replace (i + (t + r - i)) with (t + r) in H13 by lia.
              apply H13; try lia.
            + rewrite app_Znth2.
              2:{ rewrite Zlength_sublist; try lia. }
              rewrite Znth_sublist; try lia.
              rewrite Zlength_sublist; try lia.
              rewrite Znth_sublist; try lia.
              replace (t + 0) with t by lia.
              replace (t - (Zlength patn - r) + (Zlength patn - r)) with t by lia.
              reflexivity.
        }
        rewrite H17. reflexivity.
      }
      assert (is_prefix (u ++ v) (u ++ z ++ u ++ z)).
      { unfold is_prefix.
        destruct H17 as [l' H17].
        exists (l' ++ z).
        assert ((u ++ v) ++ l' = u ++ z ++ u).
        { rewrite <- app_assoc. rewrite <- H17. reflexivity. }
        rewrite (app_assoc (u ++ v) l' z).
        rewrite H18. 
        rewrite <- app_assoc. 
        rewrite <- app_assoc.
        reflexivity. }
      assert (is_period 0 (u ++ z ++ u ++ z) r).
      { assert (r = Zlength (u ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        rewrite app_assoc.
        apply is_period_spec_repeat_twice; try lia. }
      assert (is_period 0 (u ++ v) r).
      { apply (prefix_contains_period _ _ _ _ H18 H19). }
      assert (patn = u ++ v).
      { subst u. subst v. 
        rewrite <- (Zsublist_all patn) at 1.
        rewrite (sublist_split _ _ i); try lia.
        reflexivity. }
      rewrite <- H21 in H20.
      assert (is_minimal_period 0 patn p).
      { split; [split|]; try auto. }
      assert (min_local_period i r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period i r p H22 H23.
      pose proof H4 r H20.
      assert (r = p) by lia.
      rewrite <- H26. auto.
    + set (z' := skipn' (i + r) patn).
      assert (v = (z ++ u) ++ z').
      { rewrite <- app_assoc.
        subst v z u z'.
        rewrite Zlength_sublist; try lia.
        rewrite Zsublist_Zsublist; try lia.
        replace (0 + i) with i by lia.
        replace (r - (i - 0) + i) with r by lia.
        assert (sublist 0 i patn = sublist r (i + r) patn).
        { apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t Htrange.
            rewrite Zlength_sublist in Htrange; try lia.
            repeat rewrite Znth_sublist; try lia.
            specialize (H13 (t - i + r) ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (i + (t - i + r) - r) with t in H13 by lia.
            replace (i + (t - i + r)) with (t + r) in H13 by lia.
            replace (t + 0) with t by lia.
            apply H13.
        }
        rewrite H17. unfold skipn'.
        rewrite <- (sublist_split _ _ (i + r)); try lia.
        rewrite <- (sublist_split _ _ r); try lia.
        reflexivity.
      }
      set (u'' := sublist j i patn).
      assert (v' = u'' ++ v).
      { subst v' u'' v.
        rewrite <- (sublist_split _ _ i); try lia.
        reflexivity.
      }
      assert (is_suffix (u'' ++ z') patn).
      { assert (patn = u ++ v).
        { subst u v.
          rewrite <- (sublist_split _ _ i); try lia.
          rewrite Zsublist_all. reflexivity.
        }
        exists (u ++ z ++ u').
        rewrite H19. rewrite H17.
        repeat rewrite <- app_assoc.
        assert (u = u' ++ u'').
        { subst u u' u''.
          rewrite <- (sublist_split _ _ j); try lia.
          reflexivity.
        }
        rewrite H20 at 2. rewrite <- app_assoc.
        reflexivity.
      }
      assert (list_lex_ge Z Z_compare_rev v' (u'' ++ z')).
      { assert (u'' ++ z' = skipn' (Zlength patn - (i - j + Zlength v - r)) patn).
        { rewrite <- Zsublist_all in H19.
          pose proof H19 as H19'.
          apply Zsublist_suffix_inv in H19; try lia.
          rewrite H19. unfold skipn'.
          rewrite Zlength_app.
          assert (Zlength u'' + Zlength z' = i - j + Zlength v - r).
          { unfold u''. 
            rewrite Zlength_sublist; try lia.
            apply (f_equal (fun l => Zlength l)) in H17.
            rewrite Zlength_app in H17.
            rewrite <- H15 in H17.
            lia. }
          rewrite H20. reflexivity. }
        rewrite H20.
        apply H3.
        subst v. rewrite Zlength_sublist; try lia.
      }
      assert (list_lex_ge Z Z_compare_rev v z').
      { rewrite H18 in H20.
        apply (list_lex_ge_param_prefix_inv Z 0 Z_compare_rev _ _ _ Cmp_Zcompare_rev H20). }
      assert (list_lex_ge Z Z.compare v z').
      { apply H2. lia. }
      assert (is_prefix z' v).
      { apply (prefix_ordering Z 0 Z.compare Cmp_Zcompare v z'); try auto.
        apply list_lex_ge_Z_compare_rev_as_cmp_rev; auto. }
      assert (is_period 0 patn r).
      { assert (r = Zlength (u ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        assert (patn = u ++ v).
        { subst u. subst v. 
          rewrite <- (Zsublist_all patn) at 1.
          rewrite (sublist_split _ _ i); try lia.
          reflexivity. }
        rewrite H25.
        rewrite <- app_assoc in H17.
        apply (is_period_spec_repeat_prefix 0 u v z z'); try auto.
      }
      assert (is_minimal_period 0 patn p).
      { split; [split|]; try auto. }
      assert (min_local_period i r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period i r p H25 H26.
      pose proof H4 r H24.
      assert (r = p) by lia.
      rewrite <- H29. auto.
  - (* Symmetric for j: reuse i's proof with Z.compare <-> Z_compare_rev, i <-> j, u,v <-> u',v' *)
    replace (Z.max i j) with j by lia.
    assert (0 < j). { lia. }
    pose proof min_local_period_existence j ltac:(lia).
    destruct H9 as [r [? [? ?]]].
    destruct H10 as [? [? ?]].
    assert (r > j).
    { assert (r <= j \/ r > j) by lia.
      assert (r <= Zlength patn - j \/ r > Zlength patn - j) by lia.
      destruct H14; [|auto]; destruct H15.
      - set (w := sublist j (j + r) patn).
        assert (w = sublist (j - r) j patn).
        { subst w.
          apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t ?. rewrite Zlength_sublist in H16; try lia.
            repeat rewrite Znth_sublist; try lia.
            replace (t + j) with (j + t) by lia.
            replace (t + (j - r)) with (j + t - r) by lia.
            symmetry. apply (H13 t); try lia. }
        assert (is_prefix w (sublist j (Zlength patn) patn)).
        { subst w. apply Zsublist_is_prefix; try lia. }
        assert (is_suffix w (sublist 0 j patn)).
        { rewrite H16. apply Zsublist_is_suffix; try lia. }
        assert (w = nil).
        { apply (maxsuffix_cut_no_full_local_period Z_compare_rev j w Cmp_Zcompare_rev); try auto.
          split; auto. }
        assert (Zlength w = r).
        { apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_sublist in H16; try lia. }
        rewrite H19 in H20. rewrite Zlength_nil in H20.
        lia.
      - pose proof H3 (j - r) ltac:(lia).
        assert (sublist (j - r) (Zlength patn - r) patn
                = sublist j (Zlength patn) patn).
        { apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t Htrange.
            rewrite Zlength_sublist in Htrange; try lia.
            repeat rewrite Znth_sublist; try lia.
            specialize (H13 t ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (t + (j - r)) with (j + t - r) by lia.
            replace (t + j) with (j + t) by lia.
            apply H13. }
        destruct H16; [destruct H16|].
        + assert (is_proper_prefix Z (skipn' j patn) (skipn' (j - r) patn)).
          { unfold is_proper_prefix.
            split; unfold skipn'.
            - exists (sublist (Zlength patn - r) (Zlength patn) patn).
              rewrite <- H17.
              rewrite <- sublist_split; try lia.
              reflexivity.
            - repeat rewrite Zlength_sublist; try lia. }
          pose proof (proper_prefix_discriminate_gt_ex' Z Z_compare_rev _ _ Cmp_Zcompare_rev H16 H18).
          tauto.
        + unfold is_proper_prefix in H16.
          unfold skipn' in H16.
          destruct H16 as [[s ?] ?].
          apply (f_equal (fun l => Zlength l)) in H16.
          rewrite Zlength_sublist in H16; try lia.
          rewrite Zlength_app in H16.
          rewrite Zlength_sublist in H16; try lia.
          assert (0 <= Zlength s). { apply Zlength_nonneg. }
          lia.
        + apply (f_equal (fun l => Zlength l)) in H16.
          unfold skipn' in H16.
          rewrite Zlength_sublist in H16; try lia.
          rewrite Zlength_sublist in H16; try lia. }
    set (z := sublist 0 (r - Zlength u') v').
    assert (r = Zlength (z ++ u')).
    { rewrite Zlength_app. subst z. subst u'. subst v'.
      repeat rewrite Zlength_sublist; try lia. }
    assert (r > Zlength patn - j \/ r <= Zlength patn - j) by lia.
    destruct H16.
    + assert (is_prefix v' (z ++ u')).
      { unfold is_prefix.
        exists (sublist (Zlength u' + Zlength v' - r) (Zlength u') u').
        subst z. subst u'. subst v'.
        repeat rewrite Zlength_sublist; try lia.
        repeat rewrite Zsublist_Zsublist; try lia.
        simpl. replace (r - (j - 0) + j) with r by lia.
        replace (j - 0 + (Zlength patn - j) - r + 0) with (Zlength patn - r) by lia.
        replace (j - 0 + 0) with j by lia.
        rewrite (sublist_split j (Zlength patn) r); try lia.
        rewrite <- app_assoc.
        assert (sublist 0 j patn = sublist r (Zlength patn) patn
                                 ++ sublist (Zlength patn - r) j patn).
        { apply (Zsublist_eq_ext 0).
          - rewrite Zlength_app.
            repeat rewrite Zlength_sublist; try lia.
          - intros t ?.
            rewrite Zlength_sublist in H17; try lia.
            assert (t < Zlength patn - r \/ Zlength patn - r <= t) by lia.
            destruct H18.
            + rewrite app_Znth1.
              2:{ rewrite Zlength_sublist; try lia. }
              repeat rewrite Znth_sublist; try lia.
              replace (t + 0) with t by lia.
              specialize (H13 (t + r - j)).
              replace (j + (t + r - j) - r) with t in H13 by lia.
              replace (j + (t + r - j)) with (t + r) in H13 by lia.
              apply H13; try lia.
            + rewrite app_Znth2.
              2:{ rewrite Zlength_sublist; try lia. }
              rewrite Znth_sublist; try lia.
              rewrite Zlength_sublist; try lia.
              rewrite Znth_sublist; try lia.
              replace (t + 0) with t by lia.
              replace (t - (Zlength patn - r) + (Zlength patn - r)) with t by lia.
              reflexivity. }
        rewrite H17. reflexivity. }
      assert (is_prefix (u' ++ v') (u' ++ z ++ u' ++ z)).
      { unfold is_prefix.
        destruct H17 as [l' H17].
        exists (l' ++ z).
        assert ((u' ++ v') ++ l' = u' ++ z ++ u').
        { rewrite <- app_assoc. rewrite <- H17. reflexivity. }
        rewrite (app_assoc (u' ++ v') l' z).
        rewrite H18.
        rewrite <- app_assoc.
        rewrite <- app_assoc.
        reflexivity. }
      assert (is_period 0 (u' ++ z ++ u' ++ z) r).
      { assert (r = Zlength (u' ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        rewrite app_assoc.
        apply is_period_spec_repeat_twice; try lia. }
      assert (is_period 0 (u' ++ v') r).
      { apply (prefix_contains_period _ _ _ _ H18 H19). }
      assert (patn = u' ++ v').
      { subst u'. subst v'.
        rewrite <- (Zsublist_all patn) at 1.
        rewrite (sublist_split _ _ j); try lia.
        reflexivity. }
      rewrite <- H21 in H20.
      assert (is_minimal_period 0 patn p).
      { split; [split|]; try auto. }
      assert (min_local_period j r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period j r p H22 H23.
      pose proof H4 r H20.
      assert (r = p) by lia.
      rewrite <- H26. auto.
    + set (z' := skipn' (j + r) patn).
      assert (v' = (z ++ u') ++ z').
      { rewrite <- app_assoc.
        subst v' z u' z'.
        rewrite Zlength_sublist; try lia.
        rewrite Zsublist_Zsublist; try lia.
        replace (0 + j) with j by lia.
        replace (r - (j - 0) + j) with r by lia.
        assert (sublist 0 j patn = sublist r (j + r) patn).
        { apply (Zsublist_eq_ext 0).
          - repeat rewrite Zlength_sublist; try lia.
          - intros t Htrange.
            rewrite Zlength_sublist in Htrange; try lia.
            repeat rewrite Znth_sublist; try lia.
            specialize (H13 (t - j + r) ltac:(lia) ltac:(lia) ltac:(lia)).
            replace (j + (t - j + r) - r) with t in H13 by lia.
            replace (j + (t - j + r)) with (t + r) in H13 by lia.
            replace (t + 0) with t by lia.
            apply H13. }
        rewrite H17. unfold skipn'.
        rewrite <- (sublist_split _ _ (j + r)); try lia.
        rewrite <- (sublist_split _ _ r); try lia.
        reflexivity. }
      set (u'' := sublist i j patn).
      assert (v = u'' ++ v').
      { subst v u'' v'.
        rewrite <- (sublist_split _ _ j); try lia.
        reflexivity. }
      assert (is_suffix (u'' ++ z') patn).
      { assert (patn = u' ++ v').
        { subst u' v'.
          rewrite <- (sublist_split _ _ j); try lia.
          rewrite Zsublist_all. reflexivity. }
        exists (u' ++ z ++ u).
        rewrite H19. rewrite H17.
        repeat rewrite <- app_assoc.
        assert (u' = u ++ u'').
        { subst u' u u''.
          rewrite <- (sublist_split _ _ i); try lia.
          reflexivity. }
        rewrite H20 at 2. rewrite <- app_assoc.
        reflexivity. }
      assert (list_lex_ge Z Z.compare v (u'' ++ z')).
      { assert (u'' ++ z' = skipn' (Zlength patn - (j - i + Zlength v' - r)) patn).
        { rewrite <- Zsublist_all in H19.
          pose proof H19 as H19'.
          apply Zsublist_suffix_inv in H19; try lia.
          rewrite H19. unfold skipn'.
          rewrite Zlength_app.
          assert (Zlength u'' + Zlength z' = j - i + Zlength v' - r).
          { unfold u''.
            rewrite Zlength_sublist; try lia.
            apply (f_equal (fun l => Zlength l)) in H17.
            rewrite Zlength_app in H17.
            rewrite <- H15 in H17.
            lia. }
          rewrite H20. reflexivity. }
        rewrite H20.
        apply H2.
        subst v'. rewrite Zlength_sublist; try lia. }
      assert (list_lex_ge Z Z_compare_rev v' z').
      { subst z'. apply H3. lia. }
      assert (list_lex_ge Z Z.compare v' z').
      { rewrite H18 in H20. apply (list_lex_ge_param_prefix_inv Z 0 Z.compare _ _ _ Cmp_Zcompare H20). }
      assert (is_prefix z' v').
      { apply (prefix_ordering Z 0 Z.compare Cmp_Zcompare v' z'); try auto.
        apply list_lex_ge_Z_compare_rev_as_cmp_rev; auto. }
      assert (is_period 0 patn r).
      { assert (r = Zlength (u' ++ z)).
        { rewrite Zlength_app in H15.
          rewrite Zlength_app. lia. }
        assert (patn = u' ++ v').
        { subst u'. subst v'.
          rewrite <- (Zsublist_all patn) at 1.
          rewrite (sublist_split _ _ j); try lia.
          reflexivity. }
        rewrite H25.
        rewrite <- app_assoc in H17.
        apply (is_period_spec_repeat_prefix 0 u' v' z z'); try auto. }
      assert (is_minimal_period 0 patn p).
      { split; [split|]; try auto. }
      assert (min_local_period j r).
      { split; [split;[|split]|]; try auto. }
      pose proof min_local_period_le_min_period j r p H25 H26.
      pose proof H4 r H24.
      assert (r = p) by lia.
      rewrite <- H29. auto.
Qed.

Lemma maxsuf_prop_l_less_min_period (cmp_fn : Z -> Z -> comparison) (l p mp : Z) :
  Cmp Z cmp_fn ->
  is_minimal_period 0 patn mp ->
  maxsuf_prop cmp_fn l p ->
  0 <= l < mp /\ l + p <= Zlength patn.
Proof.
  intros CmpFn Hmp Hmaxsuf.
  destruct Hmaxsuf as [Hmax Hper].
  destruct Hmax as [Hlrange Hmax].
  destruct Hper as [Hper Hper_min].
  split.
  - destruct Hmp as [Hmp_per Hmp_min].
    destruct Hmp_per as [Hmp_pos Hmp_body].
    assert (l < mp \/ mp <= l) as [Hlmp | Hmpl] by lia; [lia|].
    set (l' := l - mp).
    specialize (Hmax l' ltac:(lia)).
    assert (Hgt : list_lex_gt Z cmp_fn (skipn' l' patn) (skipn' l patn)).
    { unfold list_lex_gt. right.
      unfold is_proper_prefix, skipn'.
      split.
      - exists (sublist (Zlength patn - mp) (Zlength patn) patn).
        rewrite (sublist_split l' (Zlength patn) (Zlength patn - mp)); try lia.
        subst l'.
        assert (sublist (l - mp) (Zlength patn - mp) patn =
                sublist l (Zlength patn) patn).
        { eapply (periodic_segment' 0 patn mp 1); try split; eauto; try lia. }
        rewrite H. reflexivity.
      - repeat rewrite Zlength_sublist; try lia. }
    pose proof (ge_discriminate_gt Z cmp_fn _ _ CmpFn Hmax Hgt).
    tauto.
  - assert (Hsuffix_nonempty : skipn' l patn <> nil).
    { unfold skipn'. intro Hnil.
      apply (f_equal (fun xs => Zlength xs)) in Hnil.
      rewrite Zlength_sublist in Hnil; try lia.
      rewrite Zlength_nil in Hnil.
      assert (l = Zlength patn) by lia.
      subst l.
      specialize (Hmax 0 ltac:(lia)).
      unfold skipn' in Hmax.
      rewrite Zsublist_nil in Hmax; try lia.
      rewrite Zsublist_all in Hmax.
      pose proof (list_lex_ge_nil Z cmp_fn patn) as Hnil_ge.
      pose proof (list_lex_ge_param_assym Z 0 cmp_fn patn nil CmpFn Hnil_ge Hmax) as Hpatn_nil.
      contradiction. }
    pose proof (minimal_period_le_Zlength 0 (skipn' l patn) p Hsuffix_nonempty
                  (conj Hper Hper_min)) as Hp_len.
    unfold skipn' in Hp_len.
    rewrite Zlength_sublist in Hp_len; try lia.
Qed.

Lemma maxsuf_prop_period_le_global (cmp_fn : Z -> Z -> comparison) (l p mp : Z) :
  is_minimal_period 0 patn mp ->
  maxsuf_prop cmp_fn l p ->
  p <= mp.
Proof.
  intros Hmp Hmaxsuf.
  destruct Hmaxsuf as [Hmax Hper].
  destruct Hmax as [Hlrange _].
  eapply (suffix_less_period 0 patn (skipn' l patn)).
  - unfold skipn'.
    rewrite <- (Zsublist_all patn) at 3.
    apply Zsublist_is_suffix; try lia.
  - exact Hmp.
  - exact Hper.
Qed.

Definition critical_factorization_match_prop (l p : Z) : Prop :=
  critical_factorization_prop l p /\
  (~ repetitive_split patn l p ->
   critical_factorization_prop l (Z.max l (Zlength patn - l) + 1)).

Lemma maxsuf_nonrep_shift_le_global
    (cmp_fn : Z -> Z -> comparison) (l p mp : Z) :
  Cmp Z cmp_fn ->
  is_minimal_period 0 patn mp ->
  maxsuf_prop cmp_fn l p ->
  min_local_period l mp ->
  ~ repetitive_split patn l p ->
  Z.max l (Zlength patn - l) + 1 <= mp.
Proof.
  intros CmpFn Hmp Hmaxsuf Hmmp Hnrep.
  pose proof (maxsuf_prop_l_less_min_period cmp_fn l p mp CmpFn Hmp Hmaxsuf)
    as [Hl Hlp_len].
  destruct (Z_le_gt_dec (Zlength patn - l) l) as [Hshort | Hlong].
  - replace (Z.max l (Zlength patn - l)) with l by lia.
    lia.
  - replace (Z.max l (Zlength patn - l)) with (Zlength patn - l) by lia.
    destruct (Z_le_gt_dec mp (Zlength patn - l)) as [Hmp_short | Hmp_long];
      [exfalso|lia].
    destruct Hmaxsuf as [Hmax Hper].
    assert (Hsuffix_mp : is_period 0 (skipn' l patn) mp).
    { apply (suffix_contains_period 0 patn (skipn' l patn) mp).
      - unfold is_suffix, skipn'. exists (sublist 0 l patn).
        rewrite <- (sublist_split 0 (Zlength patn) l patn); try lia.
        symmetry. apply Zsublist_all.
      - exact (proj1 Hmp). }
    destruct Hper as [Hper_period Hper_min].
    destruct Hper_period as [Hp_pos Hper_body].
    set (q := mp / p).
    set (r := mp mod p).
    assert (Hmp_div : mp = p * q + r) by
      (subst q r; apply Z.div_mod; lia).
    assert (Hp_le_mp_all : p <= mp).
    { pose proof (Hper_min mp Hsuffix_mp). lia. }
    assert (Hq_nonneg : 0 <= q).
    { subst q. apply Z.div_pos; lia. }
    assert (Hr_case : 0 < r < p \/ r = 0).
    { subst r. pose proof Z.mod_pos_bound mp p ltac:(lia). lia. }
    destruct Hr_case as [Hr_pos | Hr_zero].
    + assert (Hlocal_r : local_period l r).
      { unfold local_period.
        split; [lia|split; [lia|]].
        intros i Hi Hleft Hright.
        destruct (Z_le_gt_dec 0 (l - r)) as [Hlnonneg | Hlneg].
        - assert (Hseg_global :
            sublist (l - r) l patn = sublist (l + mp - r) (l + mp) patn).
          { eapply (periodic_segment' 0 patn mp 1).
            - exact (proj1 Hmp).
            - lia.
            - lia.
            - lia.
            - lia.
            - lia.
            - lia. }
          assert (Hseg_suffix :
            sublist l (l + r) patn = sublist (l + mp - r) (l + mp) patn).
          { set (v := skipn' l patn).
            assert (Hp_le_mp : p <= mp).
            { pose proof (Hper_min mp Hsuffix_mp). lia. }
            assert (sublist 0 r v = sublist (mp - r) mp v).
            { rewrite Hmp_div.
              eapply (periodic_segment' 0 v p q).
              - split; [exact Hp_pos|exact Hper_body].
              - lia.
              - lia.
              - unfold v, skipn'. rewrite Zlength_sublist; lia.
              - unfold v, skipn'. rewrite Zlength_sublist; lia.
              - lia.
              - lia. }
            subst v. unfold skipn' in H.
            rewrite Zsublist_Zsublist in H by lia.
            rewrite Zsublist_Zsublist in H by lia.
            simpl in H.
            replace (r + l) with (l + r) in H by lia.
            replace (mp - r + l) with (l + mp - r) in H by lia.
            replace (mp + l) with (l + mp) in H by lia.
            exact H. }
          rewrite <- Hseg_suffix in Hseg_global.
          apply (f_equal (fun xs => Znth i xs 0)) in Hseg_global.
          rewrite Znth_sublist in Hseg_global by lia.
          rewrite Znth_sublist in Hseg_global by lia.
          replace (i + (l - r)) with (l + i - r) in Hseg_global by lia.
          replace (i + l) with (l + i) in Hseg_global by lia.
          exact Hseg_global.
        - destruct (Z_le_gt_dec (l + mp) (Zlength patn)) as [Hlmp_ok | Hlmp_over].
          * assert (Hseg_suffix :
              sublist l (l + r) patn = sublist (l + mp - r) (l + mp) patn).
            { assert (H0r : 0 <= r < p) by lia.
              rewrite Hmp_div.
              replace (l + (p * q + r) - r) with (l + p * q) by lia.
              replace (l + (p * q + r)) with (l + p * q + r) by lia.
              set (v := skipn' l patn).
              assert (sublist 0 r v = sublist (p * q) (p * q + r) v).
              { eapply (periodic_segment' 0 v p q).
                - split; [exact Hp_pos|exact Hper_body].
                - lia.
                - lia.
                - unfold v, skipn'. rewrite Zlength_sublist; lia.
                - unfold v, skipn'. rewrite Zlength_sublist; lia.
                - lia.
                - lia. }
              subst v. unfold skipn' in H.
              rewrite Zsublist_Zsublist in H by lia.
              rewrite Zsublist_Zsublist in H by lia.
              simpl in H.
              replace (r + l) with (l + r) in H by lia.
              replace (p * q + l) with (l + p * q) in H by lia.
              replace (p * q + r + l) with (l + p * q + r) in H by lia.
              exact H. }
            assert (Hper_back :
              Znth (l + i - r + mp) patn 0 = Znth (l + i - r) patn 0).
            { destruct Hmp as [[Hmp_pos Hmp_body] _].
              symmetry. apply Hmp_body; lia. }
            apply (f_equal (fun xs => Znth i xs 0)) in Hseg_suffix.
            rewrite Znth_sublist in Hseg_suffix by lia.
            rewrite Znth_sublist in Hseg_suffix by lia.
            replace (i + l) with (l + i) in Hseg_suffix by lia.
            replace (i + (l + mp - r)) with (l + i - r + mp) in Hseg_suffix by lia.
            rewrite Hper_back in Hseg_suffix.
            symmetry. exact Hseg_suffix.
          * assert (Hp_le_mp : p <= mp).
            { pose proof (Hper_min mp Hsuffix_mp). lia. }
            assert (Hq_pos : 1 <= q).
            { subst q. pose proof (Z.div_str_pos mp p ltac:(lia)). lia. }
            assert (Hl_mp_minus_p : l + mp - p <= Zlength patn).
            { pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp).
              lia. }
            assert (Hshift :
              Znth (l + i) patn 0 =
              Znth (l + i - r + mp - p) patn 0).
            { set (v := skipn' l patn).
              assert (sublist 0 r v = sublist (mp - p - r) (mp - p) v).
              { rewrite Hmp_div.
                eapply (periodic_segment' 0 v p (q - 1)).
                - split; [exact Hp_pos|exact Hper_body].
                - lia.
                - lia.
                - unfold v, skipn'. rewrite Zlength_sublist; lia.
                - unfold v, skipn'. rewrite Zlength_sublist; lia.
                - lia.
                - lia. }
              subst v. unfold skipn' in H.
              rewrite Zsublist_Zsublist in H by lia.
              apply (f_equal (fun xs => Znth i xs 0)) in H.
              rewrite Znth_sublist in H by lia.
              rewrite Znth_sublist in H by lia.
              rewrite Znth_sublist in H by lia.
              replace (i + (0 + l)) with (l + i) in H by lia.
              replace (i + (mp - p - r) + l)
                with (l + i - r + mp - p) in H by lia.
              exact H. }
            assert (Hp_step :
              Znth (l + i - r + mp - p) patn 0 =
              Znth (l + i - r + mp) patn 0).
            { pose proof (Hper_body (i + mp - p - r) ltac:(lia)) as Hpstep.
              assert (i + mp - p - r + p < Zlength (skipn' l patn)).
              { unfold skipn'. rewrite Zlength_sublist; lia. }
              specialize (Hpstep H).
              unfold skipn' in Hpstep.
              rewrite Znth_sublist in Hpstep by lia.
              rewrite Znth_sublist in Hpstep by lia.
              replace (i + mp - p - r + l)
                with (l + i - r + mp - p) in Hpstep by lia.
              replace (i + mp - p - r + p + l)
                with (l + i - r + mp) in Hpstep by lia.
              exact Hpstep. }
            destruct Hmp as [[Hmp_pos Hmp_body] _].
            rewrite Hshift.
            rewrite Hp_step.
            apply Hmp_body; lia. }
      destruct Hmmp as [_ Hmin].
      specialize (Hmin r Hlocal_r).
      lia.
    + assert (Hp_lt_l_or_ge : p < l \/ p >= l) by lia.
      destruct Hp_lt_l_or_ge as [Hp_lt_l | Hp_ge_l].
      * assert (Hseg_global :
          sublist (l - p) l patn = sublist (l + mp - p) (l + mp) patn).
        { apply (periodic_segment' 0 patn mp 1); try lia.
          exact (proj1 Hmp). }
        assert (Hseg_suffix :
          sublist l (l + p) patn = sublist (l + mp - p) (l + mp) patn).
        { set (v := skipn' l patn).
          assert (sublist 0 p v = sublist (mp - p) mp v).
          { rewrite Hmp_div, Hr_zero.
            replace (p * q + 0) with (p * q) by lia.
            eapply (periodic_segment' 0 v p (q - 1)).
            - split; [exact Hp_pos|exact Hper_body].
            - lia.
            - lia.
            - unfold v, skipn'. rewrite Zlength_sublist; lia.
            - unfold v, skipn'. rewrite Zlength_sublist; lia.
            - lia.
            - lia. }
          subst v. unfold skipn' in H.
          rewrite Zsublist_Zsublist in H by lia.
          rewrite Zsublist_Zsublist in H by lia.
          simpl in H.
          replace (p + l) with (l + p) in H by lia.
          replace (mp - p + l) with (l + mp - p) in H by lia.
          replace (mp + l) with (l + mp) in H by lia.
          exact H. }
        rewrite <- Hseg_suffix in Hseg_global.
        assert (Hlocal_p : local_period l p).
        { unfold local_period.
          split; [lia|split; [lia|]].
          intros i Hi Hleft Hright.
          apply (f_equal (fun xs => Znth i xs 0)) in Hseg_global.
          rewrite Znth_sublist in Hseg_global by lia.
          rewrite Znth_sublist in Hseg_global by lia.
          replace (i + (l - p)) with (l + i - p) in Hseg_global by lia.
          replace (i + l) with (l + i) in Hseg_global by lia.
          exact Hseg_global. }
        assert (p = mp).
        { destruct Hmmp as [_ Hmin].
          specialize (Hmin p Hlocal_p).
          assert (p <= mp) by (pose proof (Hper_min mp Hsuffix_mp); lia).
          lia. }
        apply Hnrep.
        unfold repetitive_split.
        rewrite H.
        eapply (periodic_segment' 0 patn mp 1).
        -- exact (proj1 Hmp).
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
      * apply Hnrep.
        unfold repetitive_split.
        assert (Hseg_p_mp :
          sublist p (l + p) patn = sublist mp (l + mp) patn).
        { set (v := skipn' l patn).
          assert (Hp_len : p <= Zlength v).
          { pose proof (minimal_period_le_Zlength 0 v p).
            apply H; [|split; [split; [exact Hp_pos|exact Hper_body]|exact Hper_min]].
            subst v. unfold skipn'. intro Hnil.
            apply (f_equal (fun xs => Zlength xs)) in Hnil.
            assert (Hlen_side : 0 <= l <= Zlength patn /\ Zlength patn <= Zlength patn)
              by lia.
            rewrite (Zlength_sublist l (Zlength patn) patn Hlen_side) in Hnil.
            rewrite Zlength_nil in Hnil.
            lia. }
          assert (sublist (p - l) p v = sublist (mp - l) mp v).
          { rewrite Hmp_div, Hr_zero.
            replace (p * q + 0) with (p * q) by lia.
            eapply (periodic_segment' 0 v p (q - 1)).
            - split; [exact Hp_pos|exact Hper_body].
            - lia.
            - lia.
            - unfold v, skipn'. rewrite Zlength_sublist; lia.
            - unfold v, skipn'. rewrite Zlength_sublist; lia.
            - lia.
            - lia. }
          subst v. unfold skipn' in H.
          rewrite Zsublist_Zsublist in H by lia.
          rewrite Zsublist_Zsublist in H by lia.
          replace (p - l + l) with p in H by lia.
          replace (mp - l + l) with mp in H by lia.
          replace (p + l) with (l + p) in H by lia.
          replace (mp + l) with (l + mp) in H by lia.
          exact H. }
        assert (Hseg_0_mp :
          sublist 0 l patn = sublist mp (l + mp) patn).
        { apply (periodic_segment' 0 patn mp 1); try lia.
          exact (proj1 Hmp). }
        rewrite Hseg_p_mp.
        exact Hseg_0_mp.
Qed.

Lemma maxsuf_nonrep_shift_prop
    (cmp_fn : Z -> Z -> comparison) (l p mp : Z) :
  Cmp Z cmp_fn ->
  is_minimal_period 0 patn mp ->
  maxsuf_prop cmp_fn l p ->
  min_local_period l mp ->
  ~ repetitive_split patn l p ->
  critical_factorization_prop l (Z.max l (Zlength patn - l) + 1).
Proof.
  intros CmpFn Hmp Hmaxsuf Hmmp Hnrep.
  pose proof (maxsuf_prop_l_less_min_period cmp_fn l p mp CmpFn Hmp Hmaxsuf)
    as [Hl _].
  constructor.
  exists mp.
  split; [exact Hmp|].
  split; [exact Hl|].
  split; [|exact Hmmp].
  split.
  - pose proof (Zlength_nonneg patn). lia.
  - eapply maxsuf_nonrep_shift_le_global; eauto.
Qed.

Lemma maxsuf_choose_sound (ms msr p pr : Z) :
  forward_maxsuf_prop ms p ->
  reverse_maxsuf_prop msr pr ->
  Hoare
    (fun _ => True)
    (maxsuf_choose_with_ms ms msr p pr)
    (fun res _ => critical_factorization_prop (fst res) (snd res)).
Proof.
  intros Hfwd Hrev.
  unfold maxsuf_choose_with_ms.
  hoare_auto.
  - destruct minimal_period_existence as [mp [_ Hmp]].
    constructor.
    exists mp.
    unfold forward_maxsuf_prop, reverse_maxsuf_prop, maxsuf_ret_prop in *.
    split; [exact Hmp|].
    split.
    + pose proof (maxsuf_prop_l_less_min_period Z.compare (ms + 1) p mp
                    Cmp_Zcompare Hmp Hfwd) as [Hl _].
      exact Hl.
    + split.
      * destruct Hfwd as [Hfmax Hper].
        pose proof Hper as Hper_all.
        destruct Hper as [[Hp_pos _] _].
        split; [exact Hp_pos|].
        exact (maxsuf_prop_period_le_global Z.compare (ms + 1) p mp Hmp
                 {| maxsuf_is_maximal := Hfmax; maxsuf_period := Hper_all |}).
      * replace (ms + 1) with (Z.max (ms + 1) (msr + 1)) by lia.
        destruct Hfwd as [Hfmax _].
        destruct Hrev as [Hrmax _].
        eapply critical_factorization_theorem; eauto.
  - destruct minimal_period_existence as [mp [_ Hmp]].
    constructor.
    exists mp.
    unfold forward_maxsuf_prop, reverse_maxsuf_prop, maxsuf_ret_prop in *.
    split; [exact Hmp|].
    split.
    + pose proof (maxsuf_prop_l_less_min_period Z_compare_rev (msr + 1) pr mp
                    Cmp_Zcompare_rev Hmp Hrev) as [Hl _].
      exact Hl.
    + split.
      * destruct Hrev as [Hrmax Hper].
        pose proof Hper as Hper_all.
        destruct Hper as [[Hp_pos _] _].
        split; [exact Hp_pos|].
        exact (maxsuf_prop_period_le_global Z_compare_rev (msr + 1) pr mp Hmp
                 {| maxsuf_is_maximal := Hrmax; maxsuf_period := Hper_all |}).
      * replace (msr + 1) with (Z.max (ms + 1) (msr + 1)) by lia.
        destruct Hfwd as [Hfmax _].
        destruct Hrev as [Hrmax _].
        eapply critical_factorization_theorem; eauto.
Qed.

Lemma maxsuf_choose_match_sound (ms msr p pr : Z) :
  forward_maxsuf_prop ms p ->
  reverse_maxsuf_prop msr pr ->
  Hoare
    (fun _ => True)
    (maxsuf_choose_with_ms ms msr p pr)
    (fun res _ => critical_factorization_match_prop (fst res) (snd res)).
Proof.
  intros Hfwd Hrev.
  unfold maxsuf_choose_with_ms.
  hoare_auto.
  - destruct minimal_period_existence as [mp [_ Hmp]].
    unfold critical_factorization_match_prop.
    pose proof Hfwd as Hfwd_all.
    pose proof Hrev as Hrev_all.
    assert (Hmmp : min_local_period (ms + 1) mp).
    { replace (ms + 1) with (Z.max (ms + 1) (msr + 1)) by lia.
      destruct Hfwd_all as [Hfmax _].
      destruct Hrev_all as [Hrmax _].
      eapply critical_factorization_theorem; eauto. }
    split.
    + constructor.
      exists mp.
      unfold forward_maxsuf_prop, reverse_maxsuf_prop, maxsuf_ret_prop in *.
      split; [exact Hmp|].
      split.
      * pose proof (maxsuf_prop_l_less_min_period Z.compare (ms + 1) p mp
                      Cmp_Zcompare Hmp Hfwd) as [Hl _].
        exact Hl.
      * split.
        -- destruct Hfwd as [Hfmax Hper].
           pose proof Hper as Hper_all.
           destruct Hper as [[Hp_pos _] _].
           split; [exact Hp_pos|].
           exact (maxsuf_prop_period_le_global Z.compare (ms + 1) p mp Hmp
                    {| maxsuf_is_maximal := Hfmax; maxsuf_period := Hper_all |}).
        -- exact Hmmp.
    + intros Hnrep.
      eapply (maxsuf_nonrep_shift_prop Z.compare (ms + 1) p mp); eauto.
      exact Cmp_Zcompare.
  - destruct minimal_period_existence as [mp [_ Hmp]].
    unfold critical_factorization_match_prop.
    pose proof Hfwd as Hfwd_all.
    pose proof Hrev as Hrev_all.
    assert (Hmmp : min_local_period (msr + 1) mp).
    { replace (msr + 1) with (Z.max (ms + 1) (msr + 1)) by lia.
      destruct Hfwd_all as [Hfmax _].
      destruct Hrev_all as [Hrmax _].
      eapply critical_factorization_theorem; eauto. }
    split.
    + constructor.
      exists mp.
      unfold forward_maxsuf_prop, reverse_maxsuf_prop, maxsuf_ret_prop in *.
      split; [exact Hmp|].
      split.
      * pose proof (maxsuf_prop_l_less_min_period Z_compare_rev (msr + 1) pr mp
                      Cmp_Zcompare_rev Hmp Hrev) as [Hl _].
        exact Hl.
      * split.
        -- destruct Hrev as [Hrmax Hper].
           pose proof Hper as Hper_all.
           destruct Hper as [[Hp_pos _] _].
           split; [exact Hp_pos|].
           exact (maxsuf_prop_period_le_global Z_compare_rev (msr + 1) pr mp Hmp
                    {| maxsuf_is_maximal := Hrmax; maxsuf_period := Hper_all |}).
        -- exact Hmmp.
    + intros Hnrep.
      eapply (maxsuf_nonrep_shift_prop Z_compare_rev (msr + 1) pr mp); eauto.
      exact Cmp_Zcompare_rev.
Qed.

Theorem critical_factorization_prog_sound :
  Hoare
    (fun _ => True)
    (critical_factorization_prog patn)
    (fun res _ => critical_factorization_prop (fst res) (snd res)).
Proof.
  unfold critical_factorization_prog.
  eapply Hoare_bind.
  - apply maxsuf_fwd_sound.
  - intros [ms p].
    eapply Hoare_bind
      with (Q := fun res _ =>
                   forward_maxsuf_prop ms p /\
                   reverse_maxsuf_prop (fst res) (snd res)).
    + unfold Hoare. split.
      * intros res st1 st2 Hfwd Hnrm.
        split; [exact Hfwd|].
        pose proof maxsuf_rev_sound as Hrev.
        unfold Hoare in Hrev.
        destruct Hrev as [Hrev_nrm _].
        eapply Hrev_nrm; eauto.
      * intros st Hfwd Herr.
        pose proof maxsuf_rev_sound as Hrev.
        unfold Hoare in Hrev.
        destruct Hrev as [_ Hrev_err].
        eapply Hrev_err; eauto.
    + intros [msr pr].
      unfold Hoare. split.
      * intros res st1 st2 [Hfwd Hrev] Hnrm.
        pose proof (maxsuf_choose_sound ms msr p pr Hfwd Hrev) as Hchoose.
        unfold Hoare in Hchoose.
        destruct Hchoose as [Hchoose_nrm _].
        eapply Hchoose_nrm; eauto.
      * intros st [Hfwd Hrev] Herr.
        pose proof (maxsuf_choose_sound ms msr p pr Hfwd Hrev) as Hchoose.
        unfold Hoare in Hchoose.
        destruct Hchoose as [_ Hchoose_err].
        eapply Hchoose_err; eauto.
Qed.

Theorem critical_factorization_prog_match_sound :
  Hoare
    (fun _ => True)
    (critical_factorization_prog patn)
    (fun res _ => critical_factorization_match_prop (fst res) (snd res)).
Proof.
  unfold critical_factorization_prog.
  eapply Hoare_bind.
  - apply maxsuf_fwd_sound.
  - intros [ms p].
    eapply Hoare_bind
      with (Q := fun res _ =>
                   forward_maxsuf_prop ms p /\
                   reverse_maxsuf_prop (fst res) (snd res)).
    + unfold Hoare. split.
      * intros res st1 st2 Hfwd Hnrm.
        split; [exact Hfwd|].
        pose proof maxsuf_rev_sound as Hrev.
        unfold Hoare in Hrev.
        destruct Hrev as [Hrev_nrm _].
        eapply Hrev_nrm; eauto.
      * intros st Hfwd Herr.
        pose proof maxsuf_rev_sound as Hrev.
        unfold Hoare in Hrev.
        destruct Hrev as [_ Hrev_err].
        eapply Hrev_err; eauto.
    + intros [msr pr].
      unfold Hoare. split.
      * intros res st1 st2 [Hfwd Hrev] Hnrm.
        pose proof (maxsuf_choose_match_sound ms msr p pr Hfwd Hrev) as Hchoose.
        unfold Hoare in Hchoose.
        destruct Hchoose as [Hchoose_nrm _].
        eapply Hchoose_nrm; eauto.
      * intros st [Hfwd Hrev] Herr.
        pose proof (maxsuf_choose_match_sound ms msr p pr Hfwd Hrev) as Hchoose.
        unfold Hoare in Hchoose.
        destruct Hchoose as [_ Hchoose_err].
        eapply Hchoose_err; eauto.
Qed.

End CriticalFactorizationMath.
