Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

Definition LexLt (a b : list Z) : Prop :=
  (exists i, 0 <= i < Z.min (Zlength a) (Zlength b) /\
    (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
    Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

Definition IntervalMove (s:list Z) (a b:Z*Z) : Prop :=
  fst b <= fst a /\ snd a <= snd b /\ 0 <= fst b <= snd b /\ snd b < Zlength s /\
  LexLt (sublist (fst b) (snd b+1) s) (sublist (fst a) (snd a+1) s).
(* L7 representation note: IntervalPlay is a game history, not mere reachability:
   its ordered intermediate states are observed by AnnFollows and its length parity
   determines the winner.  A transitive closure would erase both facts. *)
Definition IntervalPlay (s:list Z) (k:Z) (p:list(Z*Z)) : Prop :=
  p<>[] /\ Znth 0 p (0,0)=(k,k) /\
  (forall i,0 <= i < Zlength p - 1 -> IntervalMove s (Znth i p (0,0)) (Znth (i+1) p (0,0))) /\
  ~exists q,IntervalMove s (Znth (Zlength p-1) p (0,0)) q.

Definition AnnFollows (f:list(Z*Z)->Z*Z) (p:list(Z*Z)) : Prop :=
  forall i,0 <= i < Zlength p - 1 -> Z.even i = true -> Znth(i+1)p(0,0)=f(sublist 0 (i+1) p).

Definition AnnWins (s:list Z) (k:Z) : Prop :=
  exists f,(forall hist,hist <> [] -> (exists q,IntervalMove s(Znth(Zlength hist-1)hist(0,0))q)->
    IntervalMove s(Znth(Zlength hist-1)hist(0,0))(f hist)) /\
  forall p,IntervalPlay s k p -> AnnFollows f p -> Z.even(Zlength p) = true.

Definition Pre (s:list Z) : Prop :=
  (* Every clause below is stated explicitly in the P030 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength s <= 500000 /\
       Forall (fun c => 97 <= c <= 122) s. *)
  True.

Definition Spec (s:list Z) (out:list Z) : Prop :=
  Zlength out = Zlength s /\ forall k,0 <= k < Zlength s ->
    ((Znth k out 0 = 1 /\ AnnWins s k) \/ (Znth k out 0 = 0 /\ ~AnnWins s k)).

Definition PrefixMinimum (s : list Z) (k mn : Z) : Prop :=
  0 <= k <= Zlength s /\
  ((k = 0 /\ mn = 123) \/
   (0 < k /\
    (exists j, 0 <= j < k /\ mn = Znth j s 0) /\
    forall j, 0 <= j < k -> mn <= Znth j s 0)).

Definition SpecPrefix (s : list Z) (k : Z) (out : list Z) : Prop :=
  Zlength out = k /\
  forall i, 0 <= i < k ->
    ((Znth i out 0 = 1 /\ AnnWins s i) \/
     (Znth i out 0 = 0 /\ ~ AnnWins s i)).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.ClassicalChoice.
Lemma Znth_app_left__prefix_transitions :
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
Lemma Znth_app_last__prefix_transitions :
  forall (A : Type) (l : list A) (d x : A),
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros A l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma prefix_minimum_step__prefix_transitions :
  forall s k mn,
    0 <= k < Zlength s ->
    Znth k s 0 <= 122 ->
    PrefixMinimum s k mn ->
    PrefixMinimum s (k + 1) (Z.min mn (Znth k s 0)).
Proof.
  intros s k mn Hk Hchar Hmin.
  unfold PrefixMinimum in *.
  destruct Hmin as [Hkbounds [Hzero | Hpos]].
  - destruct Hzero as [-> ->].
    split; [lia |].
    right. split; [lia |]. split.
    + exists 0. split; [lia |]. rewrite Z.min_r; lia.
    + intros j Hj. assert (j = 0) by lia. subst j.
      apply Z.le_min_r.
  - destruct Hpos as [Hkpos [[j [Hj Hmn]] Hall]].
    split; [lia |].
    right. split; [lia |]. split.
    + destruct (Z.min_spec mn (Znth k s 0)) as [[Hle Heq] | [Hlt Heq]].
      * exists j. split; [lia |]. rewrite Heq. exact Hmn.
      * exists k. split; [lia | exact Heq].
    + intros j' Hj'.
      destruct (Z.eq_dec j' k) as [-> | Hne].
      * apply Z.le_min_r.
      * eapply Z.le_trans; [apply Z.le_min_l |].
        apply Hall. lia.
Qed.
Lemma spec_prefix_snoc__prefix_transitions :
  forall s k out b,
    SpecPrefix s k out ->
    0 <= k ->
    ((b = 1 /\ AnnWins s k) \/ (b = 0 /\ ~ AnnWins s k)) ->
    SpecPrefix s (k + 1) (out ++ [b]).
Proof.
  intros s k out b [Hlen Hall] Hk Hclass.
  unfold SpecPrefix.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen. lia.
  - intros i Hi.
    destruct (Z_lt_ge_dec i k) as [Hlt | Hge].
    + rewrite Znth_app_left__prefix_transitions by (rewrite Hlen; lia).
      apply Hall. lia.
    + assert (i = k) by lia. subst i.
      assert (HZ : Znth k (out ++ [b]) 0 = b).
      { rewrite <- Hlen at 1. apply Znth_app_last__prefix_transitions. }
      rewrite HZ.
      exact Hclass.
Qed.
Lemma LexLt_cons_iff__prefix_transitions :
  forall x xs y ys,
    LexLt (x :: xs) (y :: ys) <->
    x < y \/ (x = y /\ LexLt xs ys).
Proof.
  intros x xs y ys. split.
  - intros [[i [Hi [Heq Hlt]]] | [Hlen Hpre]].
    + destruct (Z.eq_dec i 0) as [-> | Hine].
      * left. rewrite !Znth0_cons in Hlt. exact Hlt.
      * right. split.
        -- specialize (Heq 0 ltac:(lia)). rewrite !Znth0_cons in Heq. exact Heq.
        -- left. exists (i - 1). split.
           ++ rewrite !Zlength_cons in Hi.
              pose proof (Z.le_min_l (1 + Zlength xs) (1 + Zlength ys)).
              pose proof (Z.le_min_r (1 + Zlength xs) (1 + Zlength ys)). lia.
           ++ split.
              ** intros j Hj. specialize (Heq (j + 1) ltac:(lia)).
                 rewrite !Znth_cons in Heq by lia.
                 replace (j + 1 - 1) with j in Heq by lia. exact Heq.
              ** rewrite !Znth_cons in Hlt by lia. exact Hlt.
    + destruct Hpre as [tail Htail]. inversion Htail; subst.
      right. split; [reflexivity |]. right. split.
      * rewrite !Zlength_cons in Hlen. lia.
      * exists tail. reflexivity.
  - intros [Hxy | [Hxy Htail]].
    + left. exists 0. split.
      * rewrite !Zlength_cons.
        pose proof (Zlength_nonneg xs). pose proof (Zlength_nonneg ys).
        split; [lia |]. apply (proj2 (Z.min_glb_lt_iff _ _ _)). lia.
      * split; [intros; lia |]. rewrite !Znth0_cons. exact Hxy.
    + subst y. destruct Htail as [[i [Hi [Heq Hlt]]] | [Hlen Hpre]].
      * left. exists (i + 1). split.
        -- rewrite !Zlength_cons.
           pose proof (Z.le_min_l (Zlength xs) (Zlength ys)).
           pose proof (Z.le_min_r (Zlength xs) (Zlength ys)).
           split; [lia |]. apply (proj2 (Z.min_glb_lt_iff _ _ _)). lia.
        -- split.
           ++ intros j Hj. destruct (Z.eq_dec j 0) as [-> | Hj0].
              ** rewrite !Znth0_cons. reflexivity.
              ** rewrite !Znth_cons by lia. apply Heq. lia.
           ++ rewrite !Znth_cons by lia.
              replace (i + 1 - 1) with i by lia. exact Hlt.
      * right. split.
        -- rewrite !Zlength_cons. lia.
        -- destruct Hpre as [tail ->]. exists tail. reflexivity.
Qed.
Lemma LexLt_iff_list_compare__prefix_transitions :
  forall a b, LexLt a b <-> list_compare Z.compare a b = Lt.
Proof.
  induction a as [|x xs IH]; intros [|y ys].
  - unfold LexLt. simpl. split; [|discriminate].
    intros [[i [Hi _]] | [Hlen _]]; rewrite !Zlength_nil in *; lia.
  - unfold LexLt. simpl. split; [reflexivity |].
    intros _. right. split.
    + rewrite Zlength_nil, Zlength_cons. pose proof (Zlength_nonneg ys). lia.
    + exists (y :: ys). reflexivity.
  - unfold LexLt. simpl. split; [|discriminate].
    intros [[i [Hi _]] | [Hlen _]]; rewrite Zlength_nil in *.
    + pose proof (Z.le_min_r (Zlength (x :: xs)) 0). lia.
    + rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg xs). lia.
  - rewrite LexLt_cons_iff__prefix_transitions. simpl.
    destruct (Z.compare x y) eqn:Hcmp.
    + apply Z.compare_eq_iff in Hcmp. subst y. split.
      * intros [Hlt | [_ Htail]]; [lia |]. apply IH. exact Htail.
      * intros Htail. right. split; [reflexivity |]. apply IH. exact Htail.
    + apply Z.compare_lt_iff in Hcmp. split; [intros; reflexivity |].
      intros _. left. exact Hcmp.
    + apply Z.compare_gt_iff in Hcmp. split.
      * intros [Hlt | [Heq _]]; lia.
      * discriminate.
Qed.
Lemma move_from_singleton_iff_earlier_smaller__prefix_transitions :
  forall s k,
    0 <= k < Zlength s ->
    (exists b, IntervalMove s (k, k) b) <->
    exists j, 0 <= j < k /\ Znth j s 0 < Znth k s 0.
Proof.
  intros s k Hkbound. split.
  - intros [[l r] Hmove].
    unfold IntervalMove in Hmove. simpl in Hmove.
    destruct Hmove as [Hlk [Hkr [[Hl0 Hlr] [HrN Hlex]]]].
    assert (Hk : 0 <= k < Zlength s) by lia.
    rewrite (sublist_single 0 k s Hk) in Hlex.
    assert (Hseglen : Zlength (sublist l (r + 1) s) = r + 1 - l).
    { apply Zlength_sublist. lia. }
    remember (sublist l (r + 1) s) as seg eqn:Hseg.
    destruct seg as [|x xs].
    + rewrite Zlength_nil in Hseglen. lia.
    + simpl in Hlex.
      apply LexLt_cons_iff__prefix_transitions in Hlex.
      destruct Hlex as [Hx | [_ Hfalse]].
      2: apply LexLt_iff_list_compare__prefix_transitions in Hfalse;
         destruct xs; discriminate.
      assert (Hhead : x = Znth l s 0).
      { assert (HZ : Znth 0 (x :: xs) 0 = Znth l s 0).
        { rewrite Hseg. rewrite Znth_sublist; [reflexivity | lia | lia]. }
        rewrite Znth0_cons in HZ. exact HZ. }
      exists l. subst x. assert (l <> k) by (intro; subst; lia).
      split; [lia | exact Hx].
  - intros [j [[Hj0 Hjk] Hlt]].
    exists (j, k). unfold IntervalMove. simpl.
    split; [lia |]. split; [lia |]. split.
    + split; lia.
    + split; [lia |].
      left. exists 0. split.
      * rewrite !Zlength_sublist by lia.
        split; [lia |]. apply (proj2 (Z.min_glb_lt_iff _ _ _)). lia.
      * split; [intros; lia |].
        rewrite !Znth_sublist by lia.
        replace (0 + j) with j by lia.
        replace (0 + k) with k by lia.
        exact Hlt.
Qed.
Lemma Z_compare_same_trans__prefix_transitions :
  forall x y z c,
    Z.compare x y = c -> Z.compare y z = c -> Z.compare x z = c.
Proof.
  intros x y z c Hxy Hyz. destruct c.
  - apply Z.compare_eq_iff in Hxy, Hyz.
    subst. apply (proj2 (Z.compare_eq_iff _ _)). reflexivity.
  - apply Z.compare_lt_iff in Hxy, Hyz.
    apply (proj2 (Z.compare_lt_iff _ _)). eapply Z.lt_trans; eauto.
  - apply Z.compare_gt_iff in Hxy, Hyz.
    apply (proj2 (Z.compare_gt_iff _ _)). eapply Z.lt_trans; eauto.
Qed.
Lemma LexLt_trans__prefix_transitions :
  forall a b c, LexLt a b -> LexLt b c -> LexLt a c.
Proof.
  intros a b c Hab Hbc.
  apply LexLt_iff_list_compare__prefix_transitions.
  eapply (@list_compare_trans Z Z.compare Z.compare_eq_iff a b c Lt).
  - exact Z_compare_same_trans__prefix_transitions.
  - exact Z.compare_antisym.
  - apply LexLt_iff_list_compare__prefix_transitions. exact Hab.
  - apply LexLt_iff_list_compare__prefix_transitions. exact Hbc.
Qed.
Lemma LexLt_irrefl__prefix_transitions : forall a, ~ LexLt a a.
Proof.
  intros a H.
  apply LexLt_iff_list_compare__prefix_transitions in H.
  pose proof (proj2 (@list_compare_refl Z Z.compare Z.compare_eq_iff a a) eq_refl).
  congruence.
Qed.
Lemma IntervalMove_trans__prefix_transitions :
  forall s a b c,
    IntervalMove s a b -> IntervalMove s b c -> IntervalMove s a c.
Proof.
  intros s [a1 a2] [b1 b2] [c1 c2] Hab Hbc.
  unfold IntervalMove in *. simpl in *.
  destruct Hab as [Hab1 [Hab2 [[Hb0 Hb12] [HbN Hlex1]]]].
  destruct Hbc as [Hbc1 [Hbc2 [[Hc0 Hc12] [HcN Hlex2]]]].
  repeat split; try lia.
  eapply LexLt_trans__prefix_transitions; eauto.
Qed.
Lemma IntervalMove_capacity_lt__prefix_transitions :
  forall s a b,
    IntervalMove s a b ->
    fst b + (Zlength s - 1 - snd b) <
    fst a + (Zlength s - 1 - snd a).
Proof.
  intros s [a1 a2] [b1 b2] Hmove.
  unfold IntervalMove in Hmove. simpl in *.
  destruct Hmove as [Hba [Hab [[Hb0 Hb12] [HbN Hlex]]]].
  assert (b1 < a1 \/ a2 < b2).
  { destruct (Z.eq_dec b1 a1), (Z.eq_dec a2 b2); try lia.
    subst. exfalso. eapply LexLt_irrefl__prefix_transitions. exact Hlex. }
  lia.
Qed.
Lemma interval_valid_capacity_nonneg__prefix_transitions :
  forall (s : list Z) (a : Z * Z),
    0 <= fst a <= snd a -> snd a < Zlength s ->
    0 <= fst a + (Zlength s - 1 - snd a).
Proof.
  intros s [a1 a2] Hbounds Hlen.
  simpl in *. lia.
Qed.
Lemma terminal_move_from_valid__prefix_transitions :
  forall s a,
    0 <= fst a <= snd a -> snd a < Zlength s ->
    (exists b, IntervalMove s a b) ->
    exists b, IntervalMove s a b /\ ~ exists c, IntervalMove s b c.
Proof.
  intros s a Hva Hlen.
  remember (Z.to_nat (fst a + (Zlength s - 1 - snd a))) as n eqn:Hn.
  revert a Hva Hlen Hn.
  induction n as [n IH] using lt_wf_ind.
  intros a Hva Hlen Hn [b Hab].
  destruct (classic (exists c, IntervalMove s b c)) as [Hbmore | Hbterm].
  - assert (Hbv : 0 <= fst b <= snd b /\ snd b < Zlength s).
    { destruct a as [a1 a2], b as [b1 b2].
      unfold IntervalMove in Hab. simpl in *. tauto. }
    destruct Hbv as [Hbv HbN].
    assert (Hcapb : 0 <= fst b + (Zlength s - 1 - snd b))
      by (eapply interval_valid_capacity_nonneg__prefix_transitions; eauto).
    assert (Hcapa : 0 <= fst a + (Zlength s - 1 - snd a))
      by (eapply interval_valid_capacity_nonneg__prefix_transitions; eauto).
    assert (Hnatlt :
      (Z.to_nat (fst b + (Zlength s - 1 - snd b)) < n)%nat).
    { rewrite Hn. apply Z2Nat.inj_lt; try lia.
      eapply IntervalMove_capacity_lt__prefix_transitions. exact Hab. }
    destruct (IH _ Hnatlt b Hbv HbN eq_refl Hbmore) as [d [Hbd Hdterm]].
    exists d. split; [eapply IntervalMove_trans__prefix_transitions; eauto | exact Hdterm].
  - exists b. auto.
Qed.
Lemma terminal_move__prefix_transitions :
  forall s a,
    (exists b, IntervalMove s a b) ->
    exists b, IntervalMove s a b /\ ~ exists c, IntervalMove s b c.
Proof.
  intros s a [b Hab].
  destruct (classic (exists c, IntervalMove s b c)) as [Hbmore | Hbterm].
  - assert (Hbv : 0 <= fst b <= snd b /\ snd b < Zlength s).
    { destruct a as [a1 a2], b as [b1 b2].
      unfold IntervalMove in Hab. simpl in *. tauto. }
    destruct Hbv as [Hbv HbN].
    destruct (terminal_move_from_valid__prefix_transitions s b Hbv HbN Hbmore)
      as [d [Hbd Hdterm]].
    exists d. split; [eapply IntervalMove_trans__prefix_transitions; eauto | exact Hdterm].
  - exists b. auto.
Qed.
Lemma AnnWins_iff_move_from_singleton__prefix_transitions :
  forall s k, AnnWins s k <-> exists b, IntervalMove s (k, k) b.
Proof.
  intros s k. split.
  - intros [f [_ Hwin]].
    apply NNPP. intros Hnomove.
    assert (Hplay : IntervalPlay s k [(k, k)]).
    { unfold IntervalPlay. split; [discriminate |].
      split; [reflexivity |]. split.
      + intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia.
      + simpl. exact Hnomove. }
    assert (Hfollow : AnnFollows f [(k, k)]).
    { unfold AnnFollows. intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia. }
    specialize (Hwin [(k, k)] Hplay Hfollow).
    simpl in Hwin. discriminate.
  - intros Hinitial.
    assert (Hchoices : forall a : Z * Z, exists b : Z * Z,
      (exists q, IntervalMove s a q) ->
      IntervalMove s a b /\ ~ exists c, IntervalMove s b c).
    { intros a. destruct (classic (exists q, IntervalMove s a q)) as [Ha | Ha].
      + destruct (terminal_move__prefix_transitions s a Ha) as [b Hb].
        exists b. intros _. exact Hb.
      + exists (0, 0). tauto. }
    destruct (choice (fun a b : Z * Z =>
      (exists q, IntervalMove s a q) ->
      IntervalMove s a b /\ ~ exists c, IntervalMove s b c) Hchoices) as [F HF].
    exists (fun hist => F (Znth (Zlength hist - 1) hist (0, 0))).
    split.
    + intros hist Hhist [q Hq].
      specialize (HF (Znth (Zlength hist - 1) hist (0, 0))
        (ex_intro _ q Hq)). tauto.
    + intros p Hplay Hfollow.
      unfold IntervalPlay in Hplay.
      destruct Hplay as [Hpne [Hstart [Hsteps Hlast]]].
      assert (Hplen : 0 < Zlength p).
      { assert (Hnatlen : length p <> 0%nat).
        { intro Hz. apply Hpne. apply length_zero_iff_nil. exact Hz. }
        rewrite Zlength_correct. lia. }
      destruct (Z_lt_ge_dec 1 (Zlength p)) as [Hlong | Hshort].
      * assert (Hstep0 : IntervalMove s (Znth 0 p (0, 0)) (Znth 1 p (0, 0))).
        { apply Hsteps. lia. }
        unfold AnnFollows in Hfollow.
        specialize (Hfollow 0 ltac:(lia) ltac:(reflexivity)).
        change (Znth 1 p (0, 0) =
          F (Znth (Zlength (sublist 0 1 p) - 1)
            (sublist 0 1 p) (0, 0))) in Hfollow.
        assert (Hhistlen : Zlength (sublist 0 1 p) = 1).
        { rewrite Zlength_sublist by lia. lia. }
        assert (Hcurrent :
          Znth (Zlength (sublist 0 1 p) - 1) (sublist 0 1 p) (0, 0) =
          Znth 0 p (0, 0)).
        { rewrite Hhistlen. replace (1 - 1) with 0 by lia.
          rewrite Znth_sublist; [reflexivity | lia | lia]. }
        rewrite Hcurrent in Hfollow.
        pose proof (HF (Znth 0 p (0, 0))
          (ex_intro _ (Znth 1 p (0, 0)) Hstep0))
          as [_ Hchosen_terminal].
        rewrite <- Hfollow in Hchosen_terminal.
        assert (Hplenle2 : Zlength p <= 2).
        { apply Z.nlt_ge. intros Hgt.
          apply Hchosen_terminal. exists (Znth 2 p (0, 0)).
          apply Hsteps. lia. }
        assert (Hplen2 : Zlength p = 2) by lia.
        rewrite Hplen2. reflexivity.
      * assert (Hplen1 : Zlength p = 1) by lia.
        exfalso. apply Hlast. rewrite Hplen1.
        replace (1 - 1) with 0 by lia. rewrite Hstart.
        exact Hinitial.
Qed.
Lemma ann_wins_iff_prefix_min_lt__prefix_transitions :
  forall s k mn,
    0 <= k < Zlength s ->
    Znth k s 0 <= 122 ->
    PrefixMinimum s k mn ->
    (AnnWins s k <-> mn < Znth k s 0).
Proof.
  intros s k mn Hk Hchar Hmin.
  rewrite AnnWins_iff_move_from_singleton__prefix_transitions.
  rewrite (move_from_singleton_iff_earlier_smaller__prefix_transitions s k Hk).
  unfold PrefixMinimum in Hmin.
  destruct Hmin as [_ [[Hk0 Hmn] | [Hkpos [[j [Hj Hmn]] Hall]]]].
  - subst k mn. split.
    + intros [j [Hj _]]. lia.
    + lia.
  - split.
    + intros [j' [Hj' Hlt]]. specialize (Hall j' Hj'). lia.
    + intros Hlt. exists j. split; [exact Hj |]. rewrite <- Hmn. exact Hlt.
Qed.
