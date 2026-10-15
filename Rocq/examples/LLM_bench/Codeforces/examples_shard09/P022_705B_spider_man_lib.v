Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition SplitMove (a b : list Z) : Prop :=
  exists i p x, 0 <= i < Zlength a /\ x = Znth i a 0 /\ 1 <= p < x /\
    Permutation b (p :: (x - p) :: sublist 0 i a ++ sublist (i + 1) (Zlength a) a).
Definition SplitPlay (init : list Z) (p : list (list Z)) : Prop :=
  p <> [] /\ Znth 0 p [] = init /\
  (forall i,0 <= i < Zlength p - 1 -> SplitMove (Znth i p []) (Znth (i+1) p [])) /\
  Forall (fun x => x=1) (Znth (Zlength p-1) p []) /\
  (forall i,0 <= i < Zlength p-1->exists x,In x (Znth i p []) /\ x >= 2).
Definition SplitFirstFollows (f:list(list Z)->list Z) (p:list(list Z)) : Prop :=
  forall i,0 <= i < Zlength p-1->Z.even i = true->
    Znth (i+1) p []=f (sublist 0 (i+1) p).
Definition SplitFirstWins (a:list Z) : Prop :=
  exists f,(forall hist,hist <> [] -> (exists x,In x(Znth(Zlength hist-1)hist[]) /\ x >= 2)->
    SplitMove(Znth(Zlength hist-1)hist[])(f hist)) /\
  forall p, SplitPlay a p -> SplitFirstFollows f p -> Z.even (Zlength p)=true.
Definition Pre (added : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P022 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength added <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) added. *)
  True.
Definition Spec (added out : list Z) : Prop :=
  Zlength out = Zlength added /\ forall i,0 <= i < Zlength added->
    ((Znth i out 0 = 1 /\ SplitFirstWins (sublist 0 (i+1) added)) \/
     (Znth i out 0 = 2 /\ ~SplitFirstWins (sublist 0 (i+1) added))).

(** The total number of splits needed to reduce all cycles to singletons.
    This closed-form quantity is independent of any particular play. *)
Definition CycleMoveCount (added : list Z) : Z :=
  fold_right Z.add 0 added - Zlength added.

(** One output code, stated directly in terms of the parity of the number of
    forced remaining splits: 1 is the first player and 2 is the second. *)
Definition SpiderWinnerCode (moves code : Z) : Prop :=
  (code = 1 /\ Z.odd moves = true) \/
  (code = 2 /\ Z.even moves = true).

(** The mathematical effect of adding one cycle to an already summarized
    prefix. *)
Definition NextParity (par a next : Z) : Prop :=
  0 <= par <= 1 /\
  1 <= a /\
  next = Z.rem (par + (a - 1)) 2.

(** A completed output prefix and the parity summary carried to the next
    iteration.  The output relation is a property of every prefix, not a
    model of the C loop. *)
Definition SpiderPrefixState
    (added out : list Z) (par : Z) : Prop :=
  Zlength out = Zlength added /\
  0 <= par <= 1 /\
  par = Z.rem (CycleMoveCount added) 2 /\
  forall i, 0 <= i < Zlength added ->
    SpiderWinnerCode
      (CycleMoveCount (sublist 0 (i + 1) added))
      (Znth i out 0).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ClassicalEpsilon.
Lemma land_one_eq_rem_two_nonnegative__parity_foundation :
  forall z, 0 <= z -> Z.land z 1 = Z.rem z 2.
Proof.
  intros z Hz.
  change (Z.land z (Z.ones 1) = Z.rem z 2).
  rewrite Z.land_ones by lia.
  simpl.
  symmetry.
  apply Z.rem_mod_nonneg; lia.
Qed.
Lemma forall_Znth_intro__prefix_evolution :
  forall (P : Z -> Prop) (l : list Z) (d : Z),
    (forall i, 0 <= i < Zlength l -> P (Znth i l d)) ->
    Forall P l.
Proof.
  intros P l.
  induction l as [| a l IH]; intros d Hpoint.
  - constructor.
  - rewrite Zlength_cons in Hpoint.
    pose proof (Zlength_nonneg l) as Hlen_nonneg.
    constructor.
    + specialize (Hpoint 0 ltac:(lia)).
      rewrite Znth0_cons in Hpoint.
      exact Hpoint.
    + apply IH with (d := d).
      intros i Hi.
      specialize (Hpoint (i + 1) ltac:(lia)).
      rewrite Znth_cons in Hpoint by lia.
      replace (i + 1 - 1) with i in Hpoint by lia.
      exact Hpoint.
Qed.
Lemma cycle_move_count_nonnegative__prefix_evolution :
  forall added,
    Forall (fun x => 1 <= x) added ->
    0 <= CycleMoveCount added.
Proof.
  intros added Hpositive.
  unfold CycleMoveCount.
  induction added as [| a added IH].
  - simpl. lia.
  - inversion Hpositive as [| ? ? Ha Htail]; subst.
    specialize (IH Htail).
    rewrite Zlength_cons.
    simpl.
    lia.
Qed.
Lemma cycle_move_count_sublist_succ__prefix_evolution :
  forall added i,
    0 <= i < Zlength added ->
    CycleMoveCount (sublist 0 (i + 1) added) =
      CycleMoveCount (sublist 0 i added) + (Znth i added 0 - 1).
Proof.
  intros added i Hi.
  assert (Hprefix :
    sublist 0 (i + 1) added =
      sublist 0 i added ++ [Znth i added 0]).
  { rewrite (sublist_split 0 (i + 1) i added) by lia.
    rewrite (sublist_single 0 i added) by lia.
    reflexivity. }
  assert (Hfold : forall l acc,
    fold_right Z.add acc l = fold_right Z.add 0 l + acc).
  { intros l. induction l as [| a l IH]; intros acc.
    - simpl. lia.
    - simpl. rewrite IH. lia. }
  rewrite Hprefix.
  unfold CycleMoveCount.
  rewrite fold_right_app.
  rewrite Hfold.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  simpl.
  lia.
Qed.
Lemma spider_prefix_state_extend__prefix_evolution :
  forall added written par i next code,
    0 <= i < Zlength added ->
    (forall j, 0 <= j < Zlength added -> 1 <= Znth j added 0) ->
    NextParity par (Znth i added 0) next ->
    SpiderPrefixState (sublist 0 i added) written par ->
    ((code = 1 /\ next = 1) \/ (code = 2 /\ next = 0)) ->
    SpiderPrefixState
      (sublist 0 (i + 1) added) (written ++ [code]) next.
Proof.
  intros added written par i next code Hi Hpositive Hnext Hstate Hcode.
  destruct Hstate as [Hwritten [Hpar_bounds [Hpar Hwinner]]].
  destruct Hnext as [Hpar_bounds' [Ha Hnext]].
  assert (Hlen_i : Zlength (sublist 0 i added) = i)
    by (rewrite Zlength_sublist0; lia).
  assert (Hlen_succ : Zlength (sublist 0 (i + 1) added) = i + 1)
    by (rewrite Zlength_sublist0; lia).
  assert (Hwritten_len : Zlength written = i) by lia.
  assert (Hold_positive : Forall (fun x => 1 <= x) (sublist 0 i added)).
  { apply (forall_Znth_intro__prefix_evolution
      (fun x => 1 <= x) (sublist 0 i added) 0).
    intros j Hj.
    rewrite Zlength_sublist0 in Hj by lia.
    rewrite Znth_sublist0 by lia.
    apply Hpositive. lia. }
  pose proof
    (cycle_move_count_nonnegative__prefix_evolution
      (sublist 0 i added) Hold_positive) as Hold_nonnegative.
  pose proof
    (cycle_move_count_sublist_succ__prefix_evolution added i Hi) as Hstep.
  assert (Hnew_nonnegative :
    0 <= CycleMoveCount (sublist 0 (i + 1) added)) by lia.
  assert (Hnew_parity :
    next = Z.rem (CycleMoveCount (sublist 0 (i + 1) added)) 2).
  { rewrite Hstep, Hnext, Hpar.
    repeat rewrite Z.rem_mod_nonneg by lia.
    rewrite Z.add_mod_idemp_l by lia.
    reflexivity. }
  unfold SpiderPrefixState.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + rewrite Hnext.
      pose proof (Z.rem_bound_pos (par + (Znth i added 0 - 1)) 2
        ltac:(lia) ltac:(lia)).
      lia.
    + split; [exact Hnew_parity |].
      intros k Hk.
      rewrite Hlen_succ in Hk.
      destruct (Z_lt_ge_dec k i) as [Hki | Hki].
      * specialize (Hwinner k).
        rewrite Hlen_i in Hwinner.
        specialize (Hwinner ltac:(lia)).
        rewrite (Zsublist_Zsublist00 (k + 1) (i + 1) added) by lia.
        rewrite app_Znth1 by lia.
        rewrite (Zsublist_Zsublist00 (k + 1) i added) in Hwinner by lia.
        exact Hwinner.
      * assert (k = i) by lia. subst k.
        rewrite (Zsublist_Zsublist00 (i + 1) (i + 1) added) by lia.
        rewrite app_Znth2 by lia.
        replace (i - Zlength written) with 0 by lia.
        simpl.
        unfold SpiderWinnerCode.
        destruct Hcode as [[Hcode Hnext_one] | [Hcode Hnext_zero]];
          subst code.
        -- left. split; [reflexivity |].
           rewrite Zodd_mod.
           assert (Hrem :
             Z.rem (CycleMoveCount (sublist 0 (i + 1) added)) 2 = 1)
             by lia.
           rewrite Z.rem_mod_nonneg in Hrem by lia.
           rewrite Hrem. reflexivity.
        -- right. split; [reflexivity |].
           apply Z.even_spec.
           assert (Hrem :
             Z.rem (CycleMoveCount (sublist 0 (i + 1) added)) 2 = 0)
             by lia.
           rewrite Z.rem_mod_nonneg in Hrem by lia.
           apply (proj1
             (Z.mod_divide
               (CycleMoveCount (sublist 0 (i + 1) added)) 2 ltac:(lia)))
             in Hrem.
           destruct Hrem as [q Hq].
           exists q. lia.
Qed.
Lemma permutation_sum__final_result :
  forall a b : list Z, Permutation a b ->
    fold_right Z.add 0 a = fold_right Z.add 0 b.
Proof.
  intros a b Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma permutation_Zlength__final_result :
  forall {A} (a b : list A), Permutation a b -> Zlength a = Zlength b.
Proof.
  intros A a b Hperm.
  induction Hperm; repeat rewrite Zlength_cons; lia.
Qed.
Lemma fold_add_app__final_result :
  forall a b : list Z,
    fold_right Z.add 0 (a ++ b) =
    fold_right Z.add 0 a + fold_right Z.add 0 b.
Proof.
  induction a; intros b; simpl.
  - reflexivity.
  - rewrite IHa. lia.
Qed.
Lemma split_move_count_step__final_result :
  forall a b, SplitMove a b -> CycleMoveCount b = CycleMoveCount a - 1.
Proof.
  intros a b (i & p & x & Hi & Hx & Hp & Hperm).
  assert (Ha :
    a = sublist 0 i a ++ [x] ++ sublist (i + 1) (Zlength a) a).
  {
    rewrite <- (sublist_self a (Zlength a)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength a) i a) by lia.
    rewrite (sublist_split i (Zlength a) (i + 1) a) by lia.
    rewrite (sublist_single 0 i a) by lia.
    rewrite Hx.
    rewrite app_assoc.
    reflexivity.
  }
  unfold CycleMoveCount.
  change (fold_right Z.add 0 b - Zlength b =
          fold_right Z.add 0 a - Zlength a - 1).
  rewrite (permutation_sum__final_result _ _ Hperm).
  pose proof (f_equal (fun l => fold_right Z.add 0 l) Ha) as Hsum.
  repeat rewrite fold_add_app__final_result in Hsum.
  simpl in Hsum.
  rewrite Hsum.
  assert (Hlenperm :
    Zlength b =
    Zlength (p :: (x - p) :: sublist 0 i a ++
      sublist (i + 1) (Zlength a) a)).
  {
    apply permutation_Zlength__final_result.
    exact Hperm.
  }
  rewrite Hlenperm.
  rewrite !Zlength_cons, Zlength_app.
  rewrite !Zlength_sublist by lia.
  repeat rewrite fold_add_app__final_result.
  simpl.
  rewrite fold_add_app__final_result.
  lia.
Qed.
Lemma Forall_firstn__final_result {A} (P : A -> Prop) :
  forall n l, Forall P l -> Forall P (firstn n l).
Proof.
  induction n; intros [|x l] H; simpl; auto.
  inversion H; subst; constructor; auto.
Qed.
Lemma Forall_skipn__final_result {A} (P : A -> Prop) :
  forall n l, Forall P l -> Forall P (skipn n l).
Proof.
  induction n; intros [|x l] H; simpl; auto.
  inversion H; subst; auto.
Qed.
Lemma Forall_sublist__final_result {A} (P : A -> Prop) :
  forall lo hi l, Forall P l -> Forall P (sublist lo hi l).
Proof.
  intros lo hi l H.
  unfold sublist.
  apply Forall_skipn__final_result.
  apply Forall_firstn__final_result.
  exact H.
Qed.
Lemma split_move_positive__final_result :
  forall a b, Forall (fun x => 1 <= x) a -> SplitMove a b ->
    Forall (fun x => 1 <= x) b.
Proof.
  intros a b Hpos (i & p & x & Hi & Hx & Hp & Hperm).
  apply (proj2 (Forall_forall _ _)).
  intros y Hy.
  assert (Ht : Forall (fun z => 1 <= z)
    (p :: (x - p) :: sublist 0 i a ++
      sublist (i + 1) (Zlength a) a)).
  {
    repeat constructor; try lia.
    apply Forall_app.
    split; apply Forall_sublist__final_result; exact Hpos.
  }
  apply (proj1 (Forall_forall _ _) Ht).
  eapply Permutation_in; eauto.
Qed.
Lemma cycle_count_ones__final_result :
  forall a, Forall (fun x => x = 1) a -> CycleMoveCount a = 0.
Proof.
  intros a H.
  induction H; unfold CycleMoveCount in *.
  - rewrite Zlength_nil. reflexivity.
  - rewrite Zlength_cons. simpl. subst. lia.
Qed.
Lemma cycle_count_nonnegative__final_result :
  forall a, Forall (fun x => 1 <= x) a -> 0 <= CycleMoveCount a.
Proof.
  intros a H.
  induction H.
  - unfold CycleMoveCount. rewrite Zlength_nil. reflexivity.
  - unfold CycleMoveCount in *.
    rewrite Zlength_cons. simpl. lia.
Qed.
Lemma cycle_count_zero_ones__final_result :
  forall a, Forall (fun x => 1 <= x) a -> CycleMoveCount a = 0 ->
    Forall (fun x => x = 1) a.
Proof.
  intros a Hpos.
  induction Hpos; intros Hcount.
  - constructor.
  - assert (Htail : 0 <= CycleMoveCount l)
      by (apply cycle_count_nonnegative__final_result; assumption).
    assert (Hdecomp : CycleMoveCount (x :: l) = x - 1 + CycleMoveCount l).
    {
      unfold CycleMoveCount.
      rewrite Zlength_cons.
      simpl. lia.
    }
    constructor.
    + lia.
    + apply IHHpos. lia.
Qed.
Lemma decrement_telescope__final_result {A} :
  forall (measure : A -> Z) (d : A) p,
    p <> [] ->
    (forall i, 0 <= i < Zlength p - 1 ->
      measure (Znth (i + 1) p d) = measure (Znth i p d) - 1) ->
    measure (Znth (Zlength p - 1) p d) =
      measure (Znth 0 p d) - (Zlength p - 1).
Proof.
  intros measure d p Hne Hstep.
  assert (Hlen : 1 <= Zlength p).
  {
    destruct p; [contradiction|].
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg p).
    lia.
  }
  assert (Hpoint_nat : forall n : nat,
    Z.of_nat n < Zlength p ->
    measure (Znth (Z.of_nat n) p d) =
      measure (Znth 0 p d) - Z.of_nat n).
  {
    induction n; intros Hn.
    - simpl. lia.
    - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite Hstep by lia.
      rewrite IHn by lia.
      lia.
  }
  specialize (Hpoint_nat (Z.to_nat (Zlength p - 1))).
  rewrite Z2Nat.id in Hpoint_nat by lia.
  apply Hpoint_nat.
  lia.
Qed.
Lemma split_play_move_count__final_result :
  forall init play,
    Forall (fun x => 1 <= x) init ->
    SplitPlay init play ->
    Zlength play - 1 = CycleMoveCount init.
Proof.
  intros init play Hpos
    (Hne & Hfirst & Hsteps & Hfinal & Hnonterminal).
  pose proof (decrement_telescope__final_result CycleMoveCount [] play
    Hne (fun i Hi => split_move_count_step__final_result _ _ (Hsteps i Hi)))
    as Htel.
  rewrite Hfirst in Htel.
  rewrite (cycle_count_ones__final_result _ Hfinal) in Htel.
  lia.
Qed.
Lemma In_Znth_Zlength__final_result {A} :
  forall (l : list A) x d, In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  induction l as [|y l IH]; intros x d Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
      * reflexivity.
    + destruct (IH x d Hin) as (i & Hi & Hxi).
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * unfold Znth in *.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        simpl. exact Hxi.
Qed.
Lemma split_move_exists__final_result :
  forall a, (exists x, In x a /\ x >= 2) -> exists b, SplitMove a b.
Proof.
  intros a (x & Hin & Hx).
  destruct (In_Znth_Zlength__final_result a x 0 Hin) as (i & Hi & Hxi).
  exists (1 :: (x - 1) :: sublist 0 i a ++
    sublist (i + 1) (Zlength a) a).
  exists i, 1, x.
  repeat split; try lia; auto using Permutation_refl.
Qed.
Lemma positive_cycle_nonterminal__final_result :
  forall a, Forall (fun x => 1 <= x) a -> CycleMoveCount a > 0 ->
    exists x, In x a /\ x >= 2.
Proof.
  intros a Hpos Hcount.
  destruct (classic (exists x, In x a /\ x >= 2)) as [H | H]; auto.
  exfalso.
  assert (Hones : Forall (fun x => x = 1) a).
  {
    apply (proj2 (Forall_forall _ _)).
    intros x Hx.
    assert (Hxpos : 1 <= x).
    { apply (proj1 (Forall_forall _ _) Hpos x Hx). }
    assert (Hnot : ~ x >= 2) by (intros Hge; apply H; eauto).
    lia.
  }
  rewrite (cycle_count_ones__final_result _ Hones) in Hcount.
  lia.
Qed.
Lemma extend_history_first__final_result {A} :
  forall (h : list A) b d,
    h <> [] -> Znth 0 (h ++ [b]) d = Znth 0 h d.
Proof.
  intros h b d Hne.
  rewrite app_Znth1; auto.
  destruct h; [contradiction|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg h). lia.
Qed.
Lemma extend_history_last__final_result {A} :
  forall (h : list A) b d,
    Znth (Zlength (h ++ [b]) - 1) (h ++ [b]) d = b.
Proof.
  intros h b d.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength h + (1 + 0) - 1) with (Zlength h) by lia.
  rewrite app_Znth2 by lia.
  replace (Zlength h + Z.succ 0 - 1 - Zlength h) with 0 by lia.
  reflexivity.
Qed.
Lemma extend_history_steps__final_result :
  forall h b,
    h <> [] ->
    (forall i, 0 <= i < Zlength h - 1 ->
      SplitMove (Znth i h []) (Znth (i + 1) h [])) ->
    SplitMove (Znth (Zlength h - 1) h []) b ->
    forall i, 0 <= i < Zlength (h ++ [b]) - 1 ->
      SplitMove (Znth i (h ++ [b]) []) (Znth (i + 1) (h ++ [b]) []).
Proof.
  intros h b Hne Hsteps Hlast i Hi.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_ge_dec i (Zlength h - 1)) as [Hold | Hnew].
  - rewrite !app_Znth1 by lia.
    apply Hsteps. lia.
  - assert (i = Zlength h - 1) by lia. subst i.
    rewrite app_Znth1 by (destruct h; [contradiction|]; rewrite Zlength_cons;
      pose proof (Zlength_nonneg h); lia).
    replace (Zlength h - 1 + 1) with (Zlength h) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength h - Zlength h) with 0 by lia.
    exact Hlast.
Qed.
Lemma extend_history_nonterminal__final_result :
  forall h b,
    h <> [] ->
    (forall i, 0 <= i < Zlength h - 1 ->
      exists x, In x (Znth i h []) /\ x >= 2) ->
    (exists x, In x (Znth (Zlength h - 1) h []) /\ x >= 2) ->
    forall i, 0 <= i < Zlength (h ++ [b]) - 1 ->
      exists x, In x (Znth i (h ++ [b]) []) /\ x >= 2.
Proof.
  intros h b Hne Hold Hlast i Hi.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_ge_dec i (Zlength h - 1)) as [Hlt | Hge].
  - rewrite app_Znth1 by lia. apply Hold. lia.
  - assert (i = Zlength h - 1) by lia. subst i.
    rewrite app_Znth1 by (destruct h; [contradiction|]; rewrite Zlength_cons;
      pose proof (Zlength_nonneg h); lia).
    exact Hlast.
Qed.
Lemma extend_history_follows__final_result :
  forall f h,
    h <> [] ->
    SplitFirstFollows f h ->
    SplitFirstFollows f (h ++ [f h]).
Proof.
  intros f h Hne Hfollow i Hi Heven.
  unfold SplitFirstFollows in Hfollow.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_ge_dec i (Zlength h - 1)) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    rewrite sublist_split_app_l by lia.
    apply Hfollow.
    + lia.
    + exact Heven.
  - assert (i = Zlength h - 1) by lia. subst i.
    replace (Zlength h - 1 + 1) with (Zlength h) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength h - Zlength h) with 0 by lia.
    rewrite sublist_app_exact1.
    reflexivity.
Qed.
Lemma strategy_play_exists_from_history__final_result :
  forall n init f h,
    (forall hist, hist <> [] ->
      (exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2) ->
      SplitMove (Znth (Zlength hist - 1) hist []) (f hist)) ->
    h <> [] ->
    Znth 0 h [] = init ->
    (forall i, 0 <= i < Zlength h - 1 ->
      SplitMove (Znth i h []) (Znth (i + 1) h [])) ->
    SplitFirstFollows f h ->
    (forall i, 0 <= i < Zlength h - 1 ->
      exists x, In x (Znth i h []) /\ x >= 2) ->
    Forall (fun x => 1 <= x) (Znth (Zlength h - 1) h []) ->
    CycleMoveCount (Znth (Zlength h - 1) h []) = Z.of_nat n ->
    exists p, SplitPlay init p /\ SplitFirstFollows f p.
Proof.
  induction n as [|n IH]; intros init f h Hlegal Hne Hfirst Hsteps
    Hfollow Hnonterminal Hpositive Hcount.
  - exists h. split.
    + unfold SplitPlay.
      repeat split; auto.
      apply cycle_count_zero_ones__final_result; auto.
    + exact Hfollow.
  - assert (Hcountpos : CycleMoveCount
      (Znth (Zlength h - 1) h []) > 0) by (rewrite Hcount; lia).
    pose proof (positive_cycle_nonterminal__final_result _ Hpositive Hcountpos)
      as Hcurrent.
    pose proof (Hlegal h Hne Hcurrent) as Hmove.
    apply (IH init f (h ++ [f h])); auto.
    + intros Hnil.
      apply app_eq_nil in Hnil. tauto.
    + rewrite extend_history_first__final_result by exact Hne.
      exact Hfirst.
    + apply extend_history_steps__final_result; auto.
    + apply extend_history_follows__final_result; auto.
    + apply extend_history_nonterminal__final_result; auto.
    + rewrite extend_history_last__final_result.
      eapply split_move_positive__final_result; eauto.
    + rewrite extend_history_last__final_result.
      rewrite (split_move_count_step__final_result _ _ Hmove).
      rewrite Hcount.
      lia.
Qed.
Lemma even_successor_iff_odd__final_result :
  forall n, Z.even (n + 1) = true <-> Z.odd n = true.
Proof.
  intros n.
  rewrite Z.even_spec, Z.odd_spec.
  split; intros (k & Hk).
  - exists (k - 1). lia.
  - exists (k + 1). lia.
Qed.
Lemma strategy_play_exists__final_result :
  forall init f,
    init <> [] ->
    Forall (fun x => 1 <= x) init ->
    (forall hist, hist <> [] ->
      (exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2) ->
      SplitMove (Znth (Zlength hist - 1) hist []) (f hist)) ->
    exists p, SplitPlay init p /\ SplitFirstFollows f p.
Proof.
  intros init f Hne Hpos Hlegal.
  pose proof (cycle_count_nonnegative__final_result _ Hpos) as Hcount_nonneg.
  apply (strategy_play_exists_from_history__final_result
    (Z.to_nat (CycleMoveCount init)) init f [init]).
  - exact Hlegal.
  - discriminate.
  - reflexivity.
  - intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia.
  - intros i Hi Heven. rewrite Zlength_cons, Zlength_nil in Hi. lia.
  - intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia.
  - change (Forall (fun x => 1 <= x) init). exact Hpos.
  - change (CycleMoveCount init = Z.of_nat (Z.to_nat (CycleMoveCount init))).
    rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma split_first_wins_iff_odd__final_result :
  forall init,
    init <> [] ->
    Forall (fun x => 1 <= x) init ->
    (SplitFirstWins init <-> Z.odd (CycleMoveCount init) = true).
Proof.
  intros init Hinit_ne Hpositive.
  split.
  - intros (f & Hlegal & Hwins).
    destruct (strategy_play_exists__final_result init f Hinit_ne Hpositive Hlegal)
      as (play & Hplay & Hfollows).
    specialize (Hwins play Hplay Hfollows).
    pose proof (split_play_move_count__final_result init play Hpositive Hplay)
      as Hmoves.
    replace (Zlength play) with (CycleMoveCount init + 1) in Hwins by lia.
    apply (proj1 (even_successor_iff_odd__final_result _)).
    exact Hwins.
  - intros Hodd.
    assert (Htotal : forall hist : list (list Z),
      exists b, hist <> [] ->
        (exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2) ->
        SplitMove (Znth (Zlength hist - 1) hist []) b).
    {
      intros hist.
      destruct (classic (hist <> [] /\
        exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2))
        as [[Hhist Hnonterminal] | Hnone].
      - destruct (split_move_exists__final_result _ Hnonterminal) as (b & Hb).
        exists b. intros. exact Hb.
      - exists []. tauto.
    }
    set (f := fun hist =>
      proj1_sig (constructive_indefinite_description _ (Htotal hist))).
    assert (Hlegal : forall hist, hist <> [] ->
      (exists x, In x (Znth (Zlength hist - 1) hist []) /\ x >= 2) ->
      SplitMove (Znth (Zlength hist - 1) hist []) (f hist)).
    {
      intros hist Hhist Hnonterminal.
      unfold f.
      exact (proj2_sig (constructive_indefinite_description _ (Htotal hist))
        Hhist Hnonterminal).
    }
    exists f. split.
    + exact Hlegal.
    + intros play Hplay Hfollows.
      pose proof (split_play_move_count__final_result init play Hpositive Hplay)
        as Hmoves.
      replace (Zlength play) with (CycleMoveCount init + 1) by lia.
      apply (proj2 (even_successor_iff_odd__final_result _)).
      exact Hodd.
Qed.
Lemma spider_prefix_state_implies_spec__final_result :
  forall added out par,
    (forall i, 0 <= i < Zlength added -> 1 <= Znth i added 0) ->
    SpiderPrefixState added out par ->
    Spec added out.
Proof.
  intros added out par Hpositive
    (Hlength & Hpar_bounds & Hpar & Hwinners).
  assert (Hpositive_all : Forall (fun x => 1 <= x) added).
  {
    apply (proj2 (Forall_forall _ _)).
    intros x Hx.
    destruct (In_Znth_Zlength__final_result added x 0 Hx)
      as (i & Hi & <-).
    apply Hpositive. exact Hi.
  }
  unfold Spec.
  split; [exact Hlength|].
  intros i Hi.
  specialize (Hwinners i Hi).
  assert (Hprefix_positive :
    Forall (fun x => 1 <= x) (sublist 0 (i + 1) added)).
  { apply Forall_sublist__final_result. exact Hpositive_all. }
  assert (Hprefix_nonempty : sublist 0 (i + 1) added <> []).
  {
    intros Hnil.
    pose proof (Zlength_sublist 0 (i + 1) added ltac:(lia)) as Hplen.
    rewrite Hnil, Zlength_nil in Hplen.
    lia.
  }
  destruct Hwinners as [[Hcode Hodd] | [Hcode Heven]].
  - left. split; [exact Hcode|].
    apply (proj2 (split_first_wins_iff_odd__final_result _
      Hprefix_nonempty Hprefix_positive)).
    exact Hodd.
  - right. split; [exact Hcode|].
    intros Hwins.
    pose proof (proj1 (split_first_wins_iff_odd__final_result _
      Hprefix_nonempty Hprefix_positive) Hwins) as Hodd.
    rewrite <- Z.negb_even in Hodd.
    rewrite Heven in Hodd.
    discriminate.
Qed.
