Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition DownloadedAt (s q time : Z) : Z := s + (time * (q-1)) / q.
Definition CanFinishFrom (t s q start : Z) : Prop :=
  DownloadedAt s q (start + t) >= t.
Definition PlaybackStarts (t s q : Z) (starts : list Z) : Prop :=
  0 < Zlength starts /\ Znth 0 starts 0 = 0 /\
  (forall i, 0 <= i < Zlength starts-1 ->
    Znth (i+1) starts 0 - Znth i starts 0 = DownloadedAt s q (Znth (i+1) starts 0) /\
    ~ CanFinishFrom t s q (Znth i starts 0)) /\
  CanFinishFrom t s q (Znth (Zlength starts-1) starts 0).
Definition Pre (t s q : Z) : Prop := 2 <= q <= 10000 /\ 1 <= s < t /\ t <= 100000.
Definition Spec (t s q out : Z) : Prop := exists starts, PlaybackStarts t s q starts /\ out = Zlength starts.

Definition MusicLoopInvariant
    (t initial q count current : Z) : Prop :=
  0 <= count /\
  current = initial * Z.pow q count /\
  forall i,
    0 <= i < count ->
    initial * Z.pow q i < t.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Lemma Zlength_map__final_result : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__final_result : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_Zrange_aux__final_result : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__final_result : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_result. lia.
Qed.
Lemma Znth_Zrange_aux__final_result : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__final_result : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__final_result by lia. lia.
Qed.
Lemma geometric_quotient_exact__final_result : forall q i,
  1 < q -> 0 <= i ->
  (q - 1) * ((Z.pow q i - 1) / (q - 1)) = Z.pow q i - 1.
Proof.
  intros q i Hq Hi.
  assert (Hdiv : exists k, Z.pow q i - 1 = (q - 1) * k).
  {
    rewrite <- (Z2Nat.id i Hi).
    induction (Z.to_nat i) as [|n IH].
    - exists 0. simpl. ring.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      destruct IH as [k IH].
      exists (q * k + 1). nia.
  }
  destruct Hdiv as [k Hk].
  rewrite Hk.
  replace ((q - 1) * k) with (k * (q - 1)) by ring.
  rewrite Z.div_mul by lia. ring.
Qed.
Lemma geometric_quotient_step__final_result : forall q i,
  1 < q -> 0 <= i ->
  (Z.pow q (i + 1) - 1) / (q - 1) =
  q * ((Z.pow q i - 1) / (q - 1)) + 1.
Proof.
  intros q i Hq Hi.
  pose proof (geometric_quotient_exact__final_result q i Hq Hi) as Hcur.
  pose proof (geometric_quotient_exact__final_result q (i + 1) Hq ltac:(lia))
    as Hnext.
  replace (i + 1) with (Z.succ i) in * by lia.
  rewrite Z.pow_succ_r in Hnext by lia.
  rewrite Z.pow_succ_r by lia.
  apply Z.mul_reg_l with (q - 1); [lia |].
  rewrite Hnext.
  replace
    ((q - 1) * (q * ((q ^ i - 1) / (q - 1)) + 1))
    with
    (q * ((q - 1) * ((q ^ i - 1) / (q - 1))) + (q - 1))
    by ring.
  rewrite Hcur. ring.
Qed.
Lemma music_downloaded_at_start_plus__final_result : forall t initial q i,
  1 < q -> 0 <= i ->
  DownloadedAt initial q
    (initial * q * ((Z.pow q i - 1) / (q - 1)) + t) =
  initial * Z.pow q i + (t * (q - 1)) / q.
Proof.
  intros t initial q i Hq Hi.
  unfold DownloadedAt.
  replace
    ((initial * q * ((Z.pow q i - 1) / (q - 1)) + t) * (q - 1))
    with
    (t * (q - 1) +
      (initial * ((Z.pow q i - 1) / (q - 1)) * (q - 1)) * q)
    by ring.
  rewrite Z.div_add by lia.
  pose proof (geometric_quotient_exact__final_result q i Hq Hi) as Hgeom.
  nia.
Qed.
Lemma music_can_finish_at_start_iff__final_result : forall t initial q i,
  1 < q -> 0 <= i ->
  CanFinishFrom t initial q
    (initial * q * ((Z.pow q i - 1) / (q - 1))) <->
  initial * Z.pow q (i + 1) >= t.
Proof.
  intros t initial q i Hq Hi.
  unfold CanFinishFrom.
  rewrite music_downloaded_at_start_plus__final_result by assumption.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  remember (initial * Z.pow q i) as a.
  remember (t * (q - 1)) as n.
  pose proof (Z.div_mod n q ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound n q ltac:(lia)) as Hmod.
  split; intros Hfinish; nia.
Qed.
Lemma music_restart_gap__final_result : forall initial q i,
  1 < q -> 0 <= i ->
  initial * q * ((Z.pow q (i + 1) - 1) / (q - 1)) -
    initial * q * ((Z.pow q i - 1) / (q - 1)) =
  DownloadedAt initial q
    (initial * q * ((Z.pow q (i + 1) - 1) / (q - 1))).
Proof.
  intros initial q i Hq Hi.
  pose proof (geometric_quotient_step__final_result q i Hq Hi) as Hstep.
  pose proof (geometric_quotient_exact__final_result q i Hq Hi) as Hgeom.
  replace
    (initial * q * ((Z.pow q (i + 1) - 1) / (q - 1)))
    with
    (initial * q * ((Z.pow q (i + 1) - 1) / (q - 1)) + 0)
    at 2 by ring.
  rewrite music_downloaded_at_start_plus__final_result by lia.
  rewrite Z.div_0_l by lia.
  rewrite Hstep.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  replace
    (initial * q *
       (q * ((q ^ i - 1) / (q - 1)) + 1) -
       initial * q * ((q ^ i - 1) / (q - 1)))
    with
    (initial * q *
      (1 + (q - 1) * ((q ^ i - 1) / (q - 1))))
    by ring.
  rewrite Hgeom. ring.
Qed.
Lemma music_loop_invariant_implies_spec__final_result :
  forall t initial q count current,
    2 <= q ->
    1 <= initial < t ->
    current >= t ->
    MusicLoopInvariant t initial q count current ->
    Spec t initial q count.
Proof.
  intros t initial q count current Hq Hinitial Hexit Hinv.
  destruct Hinv as [Hcount [Hcurrent Hprior]].
  assert (Hcount_pos : 0 < count).
  {
    destruct (Z.eq_dec count 0) as [-> | Hne]; [simpl in Hcurrent; lia | lia].
  }
  unfold Spec.
  exists
    (map
      (fun i => initial * q * ((Z.pow q i - 1) / (q - 1)))
      (Zrange 0 count)).
  split.
  - unfold PlaybackStarts.
    rewrite Zlength_map__final_result,
      Zlength_Zrange__final_result by lia.
    split.
    + lia.
    + split.
      * rewrite Znth_map__final_result with (da := 0) by
          (rewrite Zlength_Zrange__final_result by lia; lia).
        rewrite Znth_Zrange__final_result by lia.
        simpl. rewrite Z.div_0_l by lia. ring.
      * split.
        -- intros i Hi.
           rewrite !Znth_map__final_result with (da := 0) by
             (rewrite Zlength_Zrange__final_result by lia; lia).
           rewrite !Znth_Zrange__final_result by lia.
           split.
           ++ replace (0 + (i + 1)) with (i + 1) by lia.
              replace (0 + i) with i by lia.
              apply music_restart_gap__final_result; lia.
           ++ replace (0 + i) with i by lia.
              intro Hcan.
              apply music_can_finish_at_start_iff__final_result in Hcan;
                try lia.
              specialize (Hprior (i + 1) ltac:(lia)).
              lia.
        -- rewrite Znth_map__final_result with (da := 0) by
             (rewrite Zlength_Zrange__final_result by lia; lia).
           rewrite Znth_Zrange__final_result by lia.
           replace (0 + (count - 1)) with (count - 1) by lia.
           apply music_can_finish_at_start_iff__final_result; try lia.
           replace (0 + (count - 0 - 1) + 1) with count by lia.
           rewrite <- Hcurrent. exact Hexit.
  - rewrite Zlength_map__final_result,
      Zlength_Zrange__final_result by lia.
    lia.
Qed.
