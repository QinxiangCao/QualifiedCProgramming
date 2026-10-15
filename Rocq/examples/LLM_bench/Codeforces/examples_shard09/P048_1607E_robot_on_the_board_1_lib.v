Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Delta (c : Z) : Z * Z :=
  if Z.eqb c 76 then (0, - 1) else if Z.eqb c 82 then (0, 1)
  else if Z.eqb c 85 then (- 1, 0) else (1, 0).
Definition Executes (n m : Z) (s : list Z) (start : Z * Z) (q : Z) : Prop :=
  0 <= q <= Zlength s /\ forall p, 0 <= p <= q ->
  let ds := map Delta (sublist 0 p s) in
  1 <= fst start + (fold_right Z.add 0) (map fst ds) <= n /\ 1 <= snd start + (fold_right Z.add 0) (map snd ds) <= m.
Definition Pre (n m : Z) (s : list Z) : Prop :=
  (* Stated explicitly in the P048 solver Require, so dropped here:
       1 <= Zlength s <= 1000000 /\
       Forall (fun c => c = 76 \/ c = 82 \/ c = 68 \/ c = 85) s /\
       1 <= n <= 1000000 /\
       1 <= m <= 1000000   *)
  True.

Definition Spec (n m : Z) (s : list Z) (out : Z * Z) : Prop :=
  1 <= fst out <= n /\ 1 <= snd out <= m /\ exists q,
  Executes n m s out q /\
  max_value_of_subset Z.le
    (fun q' => exists st, 1 <= fst st <= n /\ 1 <= snd st <= m /\ Executes n m s st q')
    (fun x => x) q.

Definition RowOffset (s : list Z) (q : Z) : Z :=
  (fold_right Z.add 0)
    (map fst (map Delta (sublist 0 q s))).

Definition ColOffset (s : list Z) (q : Z) : Z :=
  (fold_right Z.add 0)
    (map snd (map Delta (sublist 0 q s))).

(* [PrefixWindow] gives the geometric meaning of the loop state: [r,c] is
   the displacement after [q] commands, and the four bounds are the attained
   extrema of every displacement in that prefix (including the empty one). *)
Definition PrefixWindow
    (s : list Z) (q r c minr maxr minc maxc : Z) : Prop :=
  0 <= q <= Zlength s /\
  r = RowOffset s q /\ c = ColOffset s q /\
  minr <= 0 <= maxr /\ minc <= 0 <= maxc /\
  (forall p, 0 <= p <= q ->
     minr <= RowOffset s p <= maxr /\
     minc <= ColOffset s p <= maxc) /\
  (exists p, 0 <= p <= q /\ RowOffset s p = minr) /\
  (exists p, 0 <= p <= q /\ RowOffset s p = maxr) /\
  (exists p, 0 <= p <= q /\ ColOffset s p = minc) /\
  (exists p, 0 <= p <= q /\ ColOffset s p = maxc).

Definition WindowFits
    (n m minr maxr minc maxc : Z) : Prop :=
  maxr - minr < n /\ maxc - minc < m.

(* This is the stable exit state of the scan.  It records the extremal window
   for an optimal feasible prefix without baking the C loop into the spec. *)
Definition OptimalPrefixWindow
    (n m : Z) (s : list Z) (minr maxr minc maxc : Z) : Prop :=
  exists q r c,
    PrefixWindow s q r c minr maxr minc maxc /\
    WindowFits n m minr maxr minc maxc /\
    max_value_of_subset Z.le
      (fun q' => exists st,
         1 <= fst st <= n /\ 1 <= snd st <= m /\
         Executes n m s st q')
      (fun x => x) q.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma prefix_window_zero__initialization :
  forall s, PrefixWindow s 0 0 0 0 0 0 0.
Proof.
  intros s.
  assert (Hlen : 0 <= Zlength s) by apply Zlength_nonneg.
  assert (Hrow : RowOffset s 0 = 0).
  {
    unfold RowOffset.
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  assert (Hcol : ColOffset s 0 = 0).
  {
    unfold ColOffset.
    rewrite Zsublist_nil by lia.
    reflexivity.
  }
  unfold PrefixWindow.
  split.
  - split; [lia | exact Hlen].
  - split.
    + symmetry; exact Hrow.
    + split.
      * symmetry; exact Hcol.
      * split.
        { split; lia. }
        split.
        { split; lia. }
        split.
        {
          intros p Hp.
          assert (p = 0) by lia.
          subst p.
          repeat split; lia.
        }
        repeat split.
        { exists 0. rewrite Hrow. repeat split; lia. }
        { exists 0. rewrite Hrow. repeat split; lia. }
        { exists 0. rewrite Hcol. repeat split; lia. }
        exists 0. rewrite Hcol. repeat split; lia.
Qed.
Lemma prefix_window_step_up_new_min__up_new_min :
  forall s i r c minr maxr minc maxc,
    0 <= i < Zlength s ->
    Znth i s 0 = 85 ->
    PrefixWindow s i r c minr maxr minc maxc ->
    r - 1 < minr ->
    minc <= c <= maxc ->
    PrefixWindow s (i + 1) (r - 1) c (r - 1) maxr minc maxc.
Proof.
  intros s i r c minr maxr minc maxc Hi Hcmd Hwindow Hnewmin Hcbounds.
  unfold PrefixWindow in Hwindow |- *.
  destruct Hwindow as
      (Hiold & Hr & Hc & Hrzero & Hczero & Hall &
       Hminr & Hmaxr & Hminc & Hmaxc).
  assert (Hsub :
      sublist 0 (i + 1) s =
      sublist 0 i s ++ [Znth i s 0]).
  {
    rewrite (sublist_split 0 (i + 1) i s) by lia.
    rewrite (sublist_single 0 i s) by lia.
    reflexivity.
  }
  assert (Hrowstep : RowOffset s (i + 1) = r - 1).
  {
    unfold RowOffset in Hr |- *.
    rewrite Hsub, !map_app.
    simpl.
    fold ListLib.sum in Hr |- *.
    rewrite ListLib.sum_app.
    assert (Hdelta : Delta (Znth i s 0) = (0 - 1, 0)) by
        (rewrite Hcmd; reflexivity).
    rewrite Hdelta.
    simpl.
    rewrite Hr.
    unfold ListLib.sum.
    lia.
  }
  assert (Hcolstep : ColOffset s (i + 1) = c).
  {
    unfold ColOffset in Hc |- *.
    rewrite Hsub, !map_app.
    simpl.
    fold ListLib.sum in Hc |- *.
    rewrite ListLib.sum_app.
    assert (Hdelta : Delta (Znth i s 0) = (0 - 1, 0)) by
        (rewrite Hcmd; reflexivity).
    rewrite Hdelta.
    simpl.
    rewrite Hc.
    unfold ListLib.sum.
    lia.
  }
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hczero |].
  split.
  - intros p Hp.
    destruct (Z.eq_dec p (i + 1)) as [-> | Hneq].
    + rewrite Hrowstep, Hcolstep. split; lia.
    + assert (Hpold : 0 <= p <= i) by lia.
      specialize (Hall p Hpold) as [Hrow Hcol].
      split; lia.
  - split.
    + exists (i + 1). rewrite Hrowstep. split; lia.
    + split.
      * destruct Hmaxr as (p & Hp & Hoffset).
        exists p. split; [lia | exact Hoffset].
      * split.
        -- destruct Hminc as (p & Hp & Hoffset).
           exists p. split; [lia | exact Hoffset].
        -- destruct Hmaxc as (p & Hp & Hoffset).
           exists p. split; [lia | exact Hoffset].
Qed.
Lemma prefix_window_step_up_inside__up_inside :
  forall (s : list Z) (i r c minr maxr minc maxc : Z),
    0 <= i < Zlength s ->
    Znth i s 0 = 85 ->
    PrefixWindow s i r c minr maxr minc maxc ->
    minr <= r - 1 <= maxr ->
    minc <= c <= maxc ->
    PrefixWindow s (i + 1) (r - 1) c minr maxr minc maxc.
Proof.
  intros s i r c minr maxr minc maxc Hi Hcmd Hwindow Hrbound Hcbound.
  unfold PrefixWindow in Hwindow |- *.
  destruct Hwindow as
      [Hi_len [Hr [Hc [Hrowzero [Hcolzero [Hall
      [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]].
  assert (Hprefix :
      sublist 0 (i + 1) s = sublist 0 i s ++ [Znth i s 0]).
  {
    rewrite (sublist_split 0 (i + 1) i s) by lia.
    rewrite (sublist_single 0) by lia.
    reflexivity.
  }
  assert (Hfold : forall (xs : list Z) (acc : Z),
      fold_right Z.add acc xs = fold_right Z.add 0 xs + acc).
  {
    intros xs acc.
    induction xs as [|x xs IH]; simpl; [lia |].
    rewrite IH.
    lia.
  }
  assert (Hrowstep : RowOffset s (i + 1) = RowOffset s i - 1).
  {
    unfold RowOffset.
    rewrite Hprefix, !map_app, fold_right_app, Hcmd.
    rewrite Hfold.
    replace (fold_right Z.add 0 (map fst (map Delta [85]))) with (-1)
      by reflexivity.
    lia.
  }
  assert (Hcolstep : ColOffset s (i + 1) = ColOffset s i).
  {
    unfold ColOffset.
    rewrite Hprefix, !map_app, fold_right_app, Hcmd.
    rewrite Hfold.
    replace (fold_right Z.add 0 (map snd (map Delta [85]))) with 0
      by reflexivity.
    lia.
  }
  split; [lia |].
  split.
  - rewrite Hrowstep, <- Hr. reflexivity.
  - split.
    + rewrite Hcolstep, <- Hc. reflexivity.
    + split; [exact Hrowzero |].
      split; [exact Hcolzero |].
      split.
      * intros p Hp.
        destruct (Z.eq_dec p (i + 1)) as [-> | Hne].
        -- rewrite Hrowstep, Hcolstep.
           rewrite <- Hr, <- Hc.
           exact (conj Hrbound Hcbound).
        -- apply Hall. lia.
      * split.
        -- destruct Hminr as [p [Hp Heq]].
           exists p. split; [lia | exact Heq].
        -- split.
           ++ destruct Hmaxr as [p [Hp Heq]].
              exists p. split; [lia | exact Heq].
           ++ split.
              ** destruct Hminc as [p [Hp Heq]].
                 exists p. split; [lia | exact Heq].
              ** destruct Hmaxc as [p [Hp Heq]].
                 exists p. split; [lia | exact Heq].
Qed.
Lemma Znth_app_left__down_new_max :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__down_new_max :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma prefix_window_step_down_new_max__down_new_max :
  forall (moves : list Z) (i r c minr maxr minc maxc : Z),
    0 <= i < Zlength moves ->
    Znth i moves 0 = 68 ->
    PrefixWindow moves i r c minr maxr minc maxc ->
    maxr < r + 1 ->
    PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc maxc.
Proof.
  intros moves i r c minr maxr minc maxc Hi Hcmd Hwin Hnewmax.
  destruct Hwin as
    [Hiold [Hr [Hc [Hrzero [Hczero [Hall
      [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]].
  assert (Hprefix :
    sublist 0 (i + 1) moves = sublist 0 i moves ++ [Znth i moves 0]).
  {
    rewrite (sublist_split 0 (i + 1) i moves) by lia.
    rewrite (sublist_single 0 i moves) by lia.
    reflexivity.
  }
  assert (Hfold : forall l acc,
    fold_right Z.add acc l = fold_right Z.add 0 l + acc).
  {
    intros l. induction l as [| x xs IH]; intros acc.
    - simpl. lia.
    - simpl. rewrite IH. lia.
  }
  assert (Hrstep : RowOffset moves (i + 1) = RowOffset moves i + 1).
  {
    unfold RowOffset.
    rewrite Hprefix, !map_app, fold_right_app, Hcmd, Hfold.
    reflexivity.
  }
  assert (Hcstep : ColOffset moves (i + 1) = ColOffset moves i).
  {
    unfold ColOffset.
    rewrite Hprefix, !map_app, fold_right_app, Hcmd, Hfold.
    rewrite Z.add_0_r.
    reflexivity.
  }
  unfold PrefixWindow.
  split.
  - lia.
  - split.
    + rewrite Hrstep, <- Hr. lia.
    + split.
      * rewrite Hcstep, <- Hc. reflexivity.
      * split.
        -- lia.
        -- split.
           ++ exact Hczero.
           ++ split.
              ** intros p Hp.
                 destruct (Z.eq_dec p (i + 1)) as [-> | Hneq].
                 --- pose proof (Hall i ltac:(lia)) as Hcurrent.
                     rewrite Hrstep, Hcstep, <- Hr, <- Hc. lia.
                 --- specialize (Hall p ltac:(lia)). lia.
              ** split.
                 --- destruct Hminr as [p [Hp Heq]].
                     exists p. split; [lia | exact Heq].
                 --- split.
                     +++ exists (i + 1). repeat split; try lia.
                     +++ split.
                         *** destruct Hminc as [p [Hp Heq]].
                             exists p. split; [lia | exact Heq].
                         *** destruct Hmaxc as [p [Hp Heq]].
                             exists p. split; [lia | exact Heq].
Qed.
Lemma prefix_window_step_down_inside__down_inside :
  forall moves i r c minr maxr minc maxc,
    0 <= i < Zlength moves ->
    Znth i moves 0 = 68 ->
    PrefixWindow moves i r c minr maxr minc maxc ->
    minr <= r + 1 <= maxr ->
    minc <= c <= maxc ->
    PrefixWindow moves (i + 1) (r + 1) c minr maxr minc maxc.
Proof.
  intros moves i r c minr maxr minc maxc Hi Hcmd Hwin Hrnext Hc.
  unfold PrefixWindow in Hwin |- *.
  destruct Hwin as
      [Hiwin [Hr [Hcol [Hrzero [Hczero
      [Hall [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]].
  assert (Hsub :
      sublist 0 (i + 1) moves =
      sublist 0 i moves ++ [Znth i moves 0]).
  {
    rewrite (sublist_split 0 (i + 1) i moves) by lia.
    rewrite (sublist_single 0) by lia.
    reflexivity.
  }
  assert (Hrowstep : RowOffset moves (i + 1) = RowOffset moves i + 1).
  {
    unfold RowOffset.
    rewrite Hsub, Hcmd.
    rewrite !map_app.
    simpl.
    rewrite fold_right_app.
    simpl.
    induction (map fst (map Delta (sublist 0 i moves))) as [|x xs IH];
      simpl in *; lia.
  }
  assert (Hcolstep : ColOffset moves (i + 1) = ColOffset moves i).
  {
    unfold ColOffset.
    rewrite Hsub, Hcmd.
    rewrite !map_app.
    simpl.
    rewrite fold_right_app.
    simpl.
    lia.
  }
  split; [lia |].
  split; [rewrite Hrowstep, <- Hr; reflexivity |].
  split; [rewrite Hcolstep, <- Hcol; reflexivity |].
  split; [exact Hrzero |].
  split; [exact Hczero |].
  split.
  - intros p Hp.
    destruct (Z.eq_dec p (i + 1)) as [-> | Hneq].
    + rewrite Hrowstep, Hcolstep, <- Hr, <- Hcol.
      split; assumption.
    + apply Hall. lia.
  - destruct Hminr as [p [Hp Hpeq]].
    split.
    + exists p. split; [lia | exact Hpeq].
    + destruct Hmaxr as [p' [Hp' Hp'eq]].
      split.
      * exists p'. split; [lia | exact Hp'eq].
      * destruct Hminc as [q [Hq Hqeq]].
        split.
        -- exists q. split; [lia | exact Hqeq].
        -- destruct Hmaxc as [q' [Hq' Hq'eq]].
           exists q'. split; [lia | exact Hq'eq].
Qed.
Lemma Znth_app_last__left_impossible_low_row :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma fold_right_add_base__left_valid_row :
  forall (xs : list Z) z,
    fold_right Z.add z xs = fold_right Z.add 0 xs + z.
Proof.
  induction xs as [|x xs IH]; intros z; simpl; [lia |].
  rewrite IH.
  lia.
Qed.
Lemma nonzero_Znth_sentinel_lt__left_valid_row :
  forall (xs : list Z) i,
    0 <= i <= Zlength xs ->
    Znth i (xs ++ [0]) 0 <> 0 ->
    i < Zlength xs.
Proof.
  intros xs i [Hi0 Hile] Hnz.
  destruct (Z_lt_ge_dec i (Zlength xs)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength xs) by lia; subst i.
  rewrite app_Znth2 in Hnz by lia.
  replace (Zlength xs - Zlength xs) with 0 in Hnz by lia.
  rewrite Znth0_cons in Hnz.
  contradiction.
Qed.
Lemma prefix_window_step_left_cases__left_valid_row :
  forall s q r c minr maxr minc maxc,
    0 <= q < Zlength s ->
    Znth q s 0 = 76 ->
    PrefixWindow s q r c minr maxr minc maxc ->
    PrefixWindow s (q + 1) r (c - 1)
      minr maxr (Z.min minc (c - 1)) maxc.
Proof.
  intros s q r c minr maxr minc maxc Hq Hmove Hwindow.
  unfold PrefixWindow in Hwindow |- *.
  destruct Hwindow as
      (Hqlen & Hr & Hc & Hrzero & Hczero & Hbounds &
       Hminr & Hmaxr & Hminc & Hmaxc).
  destruct Hq as [Hq0 Hqlt].
  assert (Hrow_step : RowOffset s (q + 1) = r).
  {
    unfold RowOffset.
    rewrite (sublist_split 0 (q + 1) q s) by lia.
    rewrite (sublist_single 0 q s) by lia.
    rewrite !map_app, fold_right_app.
    simpl.
    unfold Delta.
    rewrite Hmove.
    simpl.
    change (RowOffset s q = r).
    symmetry; exact Hr.
  }
  assert (Hcol_step : ColOffset s (q + 1) = c - 1).
  {
    unfold ColOffset.
    rewrite (sublist_split 0 (q + 1) q s) by lia.
    rewrite (sublist_single 0 q s) by lia.
    rewrite !map_app, fold_right_app.
    simpl.
    unfold Delta.
    rewrite Hmove.
    simpl.
    rewrite fold_right_add_base__left_valid_row.
    change (ColOffset s q - 1 = c - 1).
    rewrite <- Hc.
    reflexivity.
  }
  assert (Hcurrent :
      minr <= r <= maxr /\ minc <= c <= maxc).
  {
    specialize (Hbounds q ltac:(lia)).
    rewrite <- Hr, <- Hc in Hbounds.
    exact Hbounds.
  }
  assert (Hnewqlen : 0 <= q + 1 <= Zlength s) by (split; lia).
  assert (Hnewczero : Z.min minc (c - 1) <= 0 <= maxc).
  {
    destruct Hczero as [Hminc0 H0maxc].
    split.
    - eapply Z.le_trans; [apply Z.le_min_l | exact Hminc0].
    - exact H0maxc.
  }
  assert (Hnewbounds : forall p, 0 <= p <= q + 1 ->
      minr <= RowOffset s p <= maxr /\
      Z.min minc (c - 1) <= ColOffset s p <= maxc).
  {
    intros p Hp.
    destruct (Z_le_gt_dec p q) as [Hpq | Hpq].
    + specialize (Hbounds p ltac:(lia)).
      destruct Hbounds as [Hrb Hcb].
      split; [exact Hrb |].
      destruct Hcb as [Hlo Hhi].
      split.
      * eapply Z.le_trans; [apply Z.le_min_l | exact Hlo].
      * exact Hhi.
    + assert (p = q + 1) by lia; subst p.
      rewrite Hrow_step, Hcol_step.
      destruct Hcurrent as [Hrb Hcb].
      split; [exact Hrb |].
      destruct Hcb as [_ Hchi].
      split; [apply Z.le_min_r | lia].
  }
  assert (Hnewminr : exists p, 0 <= p <= q + 1 /\ RowOffset s p = minr).
  {
    destruct Hminr as (p & [Hp0 Hpq] & Heq).
    exists p; split; [split; lia | exact Heq].
  }
  assert (Hnewmaxr : exists p, 0 <= p <= q + 1 /\ RowOffset s p = maxr).
  {
    destruct Hmaxr as (p & [Hp0 Hpq] & Heq).
    exists p; split; [split; lia | exact Heq].
  }
  assert (Hnewminc : exists p, 0 <= p <= q + 1 /\
      ColOffset s p = Z.min minc (c - 1)).
  {
    destruct (Z_le_dec minc (c - 1)) as [Hle | Hlt].
    + rewrite Z.min_l by exact Hle.
      destruct Hminc as (p & [Hp0 Hpq] & Heq).
      exists p; split; [split; lia | exact Heq].
    + rewrite Z.min_r by lia.
      exists (q + 1); split; [split; lia | exact Hcol_step].
  }
  assert (Hnewmaxc : exists p, 0 <= p <= q + 1 /\ ColOffset s p = maxc).
  {
    destruct Hmaxc as (p & [Hp0 Hpq] & Heq).
    exists p; split; [split; lia | exact Heq].
  }
  exact (conj Hnewqlen
    (conj (eq_sym Hrow_step)
      (conj (eq_sym Hcol_step)
        (conj Hrzero
          (conj Hnewczero
            (conj Hnewbounds
              (conj Hnewminr
                (conj Hnewmaxr
                  (conj Hnewminc Hnewmaxc))))))))).
Qed.
Lemma fold_right_Z_add_base__right_valid_row :
  forall (l : list Z) z,
    fold_right Z.add z l = fold_right Z.add 0 l + z.
Proof.
  induction l as [|x l IH]; intros z; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma row_col_offset_step_right__right_valid_row :
  forall s i,
    0 <= i < Zlength s ->
    Znth i s 0 = 82 ->
    RowOffset s (i + 1) = RowOffset s i /\
    ColOffset s (i + 1) = ColOffset s i + 1.
Proof.
  intros s i Hi Hright.
  assert (Hsub : sublist 0 (i + 1) s = sublist 0 i s ++ [Znth i s 0]).
  {
    rewrite (sublist_split 0 (i + 1) i s) by lia.
    rewrite (sublist_single 0) by lia.
    reflexivity.
  }
  unfold RowOffset, ColOffset.
  rewrite Hsub, !map_app, Hright.
  simpl Delta; simpl map.
  rewrite !fold_right_app; simpl.
  split.
  - reflexivity.
  - rewrite fold_right_Z_add_base__right_valid_row. lia.
Qed.
Lemma prefix_window_step_right_cases__right_valid_row :
  forall s i r c minr maxr minc maxc,
    PrefixWindow s i r c minr maxr minc maxc ->
    i < Zlength s ->
    Znth i s 0 = 82 ->
    minr <= r <= maxr ->
    (maxc < c + 1 ->
       PrefixWindow s (i + 1) r (c + 1) minr maxr minc (c + 1)) /\
    (minc <= c + 1 <= maxc ->
       PrefixWindow s (i + 1) r (c + 1) minr maxr minc maxc).
Proof.
  intros s i r c minr maxr minc maxc Hpw Hi Hright Hrwin.
  destruct Hpw as
      [Hi_range [Hr [Hc [Hrow0 [Hcol0 [Hall
      [Hminr [Hmaxr [Hminc Hmaxc]]]]]]]]].
  pose proof (row_col_offset_step_right__right_valid_row s i
                (conj (proj1 Hi_range) Hi) Hright) as [Hrowstep Hcolstep].
  split.
  - intros Hnewmax.
    unfold PrefixWindow.
    split.
    + lia.
    + split.
      * rewrite Hrowstep. exact Hr.
      * split.
        -- rewrite Hcolstep. lia.
        -- split.
           ++ exact Hrow0.
           ++ split.
              ** lia.
              ** split.
                 --- intros p Hp.
                     destruct (Z_le_gt_dec p i) as [Hpi | Hpi].
                     +++ destruct (Hall p ltac:(lia)) as [Hrp Hcp].
                         split; [exact Hrp | lia].
                     +++ assert (p = i + 1) by lia. subst p.
                         rewrite Hrowstep, Hcolstep.
                         split; lia.
                 --- split.
                     +++ destruct Hminr as [p [Hp Heq]].
                         exists p. split; [lia | exact Heq].
                     +++ split.
                         *** destruct Hmaxr as [p [Hp Heq]].
                             exists p. split; [lia | exact Heq].
                         *** split.
                             { destruct Hminc as [p [Hp Heq]].
                               exists p. split; [lia | exact Heq]. }
                             { exists (i + 1). split; [lia |].
                               rewrite Hcolstep. lia. }
  - intros Hinside.
    unfold PrefixWindow.
    split.
    + lia.
    + split.
      * rewrite Hrowstep. exact Hr.
      * split.
        -- rewrite Hcolstep. lia.
        -- split.
           ++ exact Hrow0.
           ++ split.
              ** exact Hcol0.
              ** split.
                 --- intros p Hp.
                     destruct (Z_le_gt_dec p i) as [Hpi | Hpi].
                     +++ specialize (Hall p). apply Hall. lia.
                     +++ assert (p = i + 1) by lia. subst p.
                         rewrite Hrowstep, Hcolstep.
                         split; lia.
                 --- split.
                     +++ destruct Hminr as [p [Hp Heq]].
                         exists p. split; [lia | exact Heq].
                     +++ split.
                         *** destruct Hmaxr as [p [Hp Heq]].
                             exists p. split; [lia | exact Heq].
                         *** split.
                             { destruct Hminc as [p [Hp Heq]].
                               exists p. split; [lia | exact Heq]. }
                             { destruct Hmaxc as [p [Hp Heq]].
                               exists p. split; [lia | exact Heq]. }
Qed.
Lemma Znth_app_left__termination_optimality :
  forall (A : Type) (l1 l2 : list A) (d : A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma feasible_prefix_iff_window_fits__termination_optimality :
  forall n m s q r c minr maxr minc maxc,
    PrefixWindow s q r c minr maxr minc maxc ->
    (WindowFits n m minr maxr minc maxc <->
     exists st,
       1 <= fst st <= n /\ 1 <= snd st <= m /\
       Executes n m s st q).
Proof.
  intros n m s q r c minr maxr minc maxc HP.
  split.
  - intros HF.
    unfold PrefixWindow in HP.
    destruct HP as
      (Hq & Hr & Hc & [Hminr0 Hmaxr0] & [Hminc0 Hmaxc0] &
       Hall & Hminrw & Hmaxrw & Hmincw & Hmaxcw).
    unfold WindowFits in HF.
    destruct HF as [HFrow HFcol].
    exists (1 - minr, 1 - minc).
    change
      ((1 <= 1 - minr <= n) /\
       (1 <= 1 - minc <= m) /\
       Executes n m s (1 - minr, 1 - minc) q).
    split; [lia |].
    split; [lia |].
    unfold Executes.
    split; [exact Hq |].
    intros p Hp.
    specialize (Hall p Hp).
    destruct Hall as [[Hrowlo Hrowhi] [Hcollo Hcolhi]].
    change
      (1 <= 1 - minr + RowOffset s p <= n /\
       1 <= 1 - minc + ColOffset s p <= m).
    lia.
  - intros (st & Hstrow & Hstcol & HE).
    unfold PrefixWindow in HP.
    destruct HP as
      (Hq & Hr & Hc & Hrzero & Hczero & Hall &
       (pminr & Hpminr & Epminr) &
       (pmaxr & Hpmaxr & Epmaxr) &
       (pminc & Hpminc & Epminc) &
       (pmaxc & Hpmaxc & Epmaxc)).
    unfold Executes in HE.
    destruct HE as [HEq HEall].
    specialize (HEall pminr Hpminr) as HEminr.
    specialize (HEall pmaxr Hpmaxr) as HEmaxr.
    specialize (HEall pminc Hpminc) as HEminc.
    specialize (HEall pmaxc Hpmaxc) as HEmaxc.
    change
      (1 <= fst st + RowOffset s pminr <= n /\
       1 <= snd st + ColOffset s pminr <= m) in HEminr.
    change
      (1 <= fst st + RowOffset s pmaxr <= n /\
       1 <= snd st + ColOffset s pmaxr <= m) in HEmaxr.
    change
      (1 <= fst st + RowOffset s pminc <= n /\
       1 <= snd st + ColOffset s pminc <= m) in HEminc.
    change
      (1 <= fst st + RowOffset s pmaxc <= n /\
       1 <= snd st + ColOffset s pmaxc <= m) in HEmaxc.
    unfold WindowFits.
    rewrite Epminr in HEminr.
    rewrite Epmaxr in HEmaxr.
    rewrite Epminc in HEminc.
    rewrite Epmaxc in HEmaxc.
    lia.
Qed.
Lemma optimal_prefix_at_end__termination_optimality :
  forall n m s q r c minr maxr minc maxc,
    q = Zlength s ->
    PrefixWindow s q r c minr maxr minc maxc ->
    WindowFits n m minr maxr minc maxc ->
    OptimalPrefixWindow n m s minr maxr minc maxc.
Proof.
  intros n m s q r c minr maxr minc maxc Hq HP HF.
  unfold OptimalPrefixWindow.
  exists q, r, c.
  split; [exact HP |].
  split; [exact HF |].
  unfold max_value_of_subset, max_object_of_subset.
  exists q.
  split.
  - split.
    + apply
        (proj1
           (feasible_prefix_iff_window_fits__termination_optimality
              n m s q r c minr maxr minc maxc HP)).
      exact HF.
    + intros q' (st & Hstrow & Hstcol & HE).
      unfold Executes in HE.
      destruct HE as [[Hq'0 Hq'len] HEall].
      lia.
  - reflexivity.
Qed.
Lemma optimal_prefix_before_overflow__termination_optimality :
  forall n m s i oldr oldc r c
         minr maxr minc maxc nminr nmaxr nminc nmaxc,
    PrefixWindow s i oldr oldc minr maxr minc maxc ->
    WindowFits n m minr maxr minc maxc ->
    PrefixWindow s (i + 1) r c nminr nmaxr nminc nmaxc ->
    (nmaxr - nminr >= n \/ nmaxc - nminc >= m) ->
    OptimalPrefixWindow n m s minr maxr minc maxc.
Proof.
  intros n m s i oldr oldc r c
         minr maxr minc maxc nminr nmaxr nminc nmaxc
         HP HF HPnext Hover.
  unfold OptimalPrefixWindow.
  exists i, oldr, oldc.
  split; [exact HP |].
  split; [exact HF |].
  unfold max_value_of_subset, max_object_of_subset.
  exists i.
  split.
  - split.
    + apply
        (proj1
           (feasible_prefix_iff_window_fits__termination_optimality
              n m s i oldr oldc minr maxr minc maxc HP)).
      exact HF.
    + intros q' (st & Hstrow & Hstcol & HE).
      destruct (Z_le_gt_dec q' i) as [Hle | Hgt]; [exact Hle |].
      unfold PrefixWindow in HPnext.
      destruct HPnext as
        (Hnextq & Hnextr & Hnextc & Hnextrowzero & Hnextcolzero & Hnextall &
         (pminr & Hpminr & Epminr) &
         (pmaxr & Hpmaxr & Epmaxr) &
         (pminc & Hpminc & Epminc) &
         (pmaxc & Hpmaxc & Epmaxc)).
      unfold Executes in HE.
      destruct HE as [HEq HEall].
      assert (Hpminr' : 0 <= pminr <= q') by lia.
      assert (Hpmaxr' : 0 <= pmaxr <= q') by lia.
      assert (Hpminc' : 0 <= pminc <= q') by lia.
      assert (Hpmaxc' : 0 <= pmaxc <= q') by lia.
      specialize (HEall pminr Hpminr') as HEminr.
      specialize (HEall pmaxr Hpmaxr') as HEmaxr.
      specialize (HEall pminc Hpminc') as HEminc.
      specialize (HEall pmaxc Hpmaxc') as HEmaxc.
      change
        (1 <= fst st + RowOffset s pminr <= n /\
         1 <= snd st + ColOffset s pminr <= m) in HEminr.
      change
        (1 <= fst st + RowOffset s pmaxr <= n /\
         1 <= snd st + ColOffset s pmaxr <= m) in HEmaxr.
      change
        (1 <= fst st + RowOffset s pminc <= n /\
         1 <= snd st + ColOffset s pminc <= m) in HEminc.
      change
        (1 <= fst st + RowOffset s pmaxc <= n /\
         1 <= snd st + ColOffset s pmaxc <= m) in HEmaxc.
      rewrite Epminr in HEminr.
      rewrite Epmaxr in HEmaxr.
      rewrite Epminc in HEminc.
      rewrite Epmaxc in HEmaxc.
      lia.
  - reflexivity.
Qed.
Lemma optimal_window_realizes_spec__final_result :
  forall n m s minr maxr minc maxc,
    OptimalPrefixWindow n m s minr maxr minc maxc ->
    Spec n m s (1 - minr, 1 - minc).
Proof.
  intros n m s minr maxr minc maxc Hopt.
  unfold OptimalPrefixWindow in Hopt.
  destruct Hopt as (q & r & c & Hwindow & Hfits & Hmax).
  unfold PrefixWindow in Hwindow.
  destruct Hwindow as
      (Hq & Hr & Hc & Hrzero & Hczero & Hall & Hminr & Hmaxr & Hminc & Hmaxc).
  destruct Hrzero as [Hminr0 Hmaxr0].
  destruct Hczero as [Hminc0 Hmaxc0].
  unfold WindowFits in Hfits.
  destruct Hfits as [Hfitr Hfitc].
  unfold Spec.
  change
    ((1 <= 1 - minr <= n) /\
     (1 <= 1 - minc <= m) /\
     exists q0,
       Executes n m s (1 - minr, 1 - minc) q0 /\
       max_value_of_subset Z.le
         (fun q' => exists st,
            1 <= fst st <= n /\ 1 <= snd st <= m /\ Executes n m s st q')
         (fun x => x) q0).
  split; [lia |].
  split; [lia |].
  exists q.
    split.
    + unfold Executes.
      split; [exact Hq |].
      intros p Hp.
      specialize (Hall p Hp).
      unfold RowOffset, ColOffset in Hall.
      change
        (1 <= 1 - minr +
           fold_right Z.add 0
             (map fst (map Delta (sublist 0 p s))) <= n /\
         1 <= 1 - minc +
           fold_right Z.add 0
             (map snd (map Delta (sublist 0 p s))) <= m).
      lia.
    + exact Hmax.
Qed.
