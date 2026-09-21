From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
From SumLib Require Import Sum ZRange.
From SetsClass Require Import SetsClass.

Import ListNotations.
Local Open Scope Z_scope.

(* A market state contains cash, unused scrolls, and item statuses:
   0 = unsold/unidentified, 1 = unsold/identified, 2 = sold. *)
Definition MagicTrade (c : Z) (a b : list Z)
    (before after : Z * (Z * list Z)) : Prop :=
  let '(cash, (scrolls, items)) := before in
  (c <= cash /\ after = (cash - c, (scrolls + 1, items))) \/
  (exists i, 0 <= i < Zlength a /\
    Znth i items 0 = 0 /\ Znth i a 0 < Znth i b 0 /\
    1 <= scrolls /\
    after = (cash, (scrolls - 1, replace_Znth i 1 items))) \/
  (exists i, 0 <= i < Zlength a /\
    ((Znth i items 0 = 0 /\
      after = (cash + Znth i a 0, (scrolls, replace_Znth i 2 items))) \/
     (Znth i items 0 = 1 /\
      after = (cash + Znth i b 0, (scrolls, replace_Znth i 2 items))))).

Definition MaximumMagicRevenue (c : Z) (a b : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun cash : Z => exists scrolls items,
      SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
        (0, (0, map (fun _ : Z => 0) a)) (cash, (scrolls, items)) /\
      Forall (eq 2) items)
    (fun cash => cash) answer.

(* Revenue if identification purchases had no initial cash restriction. *)
Definition UnconstrainedRevenue (c : Z) (a b : list Z) : Z :=
  ListLib.sum (map (fun p : Z * Z => Z.max (fst p) (snd p - c))
    (combine a b)).

(* Cash from items whose identification cannot increase the final revenue. *)
Definition FreeCash (c : Z) (a b : list Z) : Z :=
  ListLib.sum (map (fun p : Z * Z =>
    if Z.leb (snd p - fst p - c) 0 then fst p else 0) (combine a b)).

(* Selecting some profitable items to sell without identification raises
   capital and sacrifices exactly their forgone identification profits.
   The extra candidate represents a capped infinity for an empty selection
   domain; all actual losses are below it on the stated input ranges. *)
Definition MinimumSacrifice (c : Z) (a b : list Z)
    (upto capital loss : Z) : Prop :=
  min_value_of_subset Z.le
    (fun value : Z => value = 10000001 \/
      exists selected : Z -> Prop,
        (forall i, 0 <= i < upto -> selected i ->
          0 < Znth i b 0 - Znth i a 0 - c) /\
        capital <= Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
          (fun i => Znth i a 0) /\
        value = Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
          (fun i => Znth i b 0 - Znth i a 0 - c))
    (fun value => value) loss.

From Coq Require Import Lia.
Lemma magic_rt_invariant__maximum_revenue {A : Type}
    (R : A -> A -> Prop) (P : A -> Prop) :
  (forall x y, P x -> R x y -> P y) ->
  forall x y, SetsClass.RelsDomain.clos_refl_trans R x y -> P x -> P y.
Proof.
  intros Hstep x y [n Hn]. revert x y Hn.
  induction n as [|n IH]; intros x y Hn HP.
  - change (x = y) in Hn. subst. exact HP.
  - destruct Hn as [z [Hx Hz]]. eapply IH; [exact Hz|].
    eapply Hstep; eauto.
Qed.
Lemma magic_rt_step__maximum_revenue {A : Type} (R : A -> A -> Prop) x y :
  R x y -> SetsClass.RelsDomain.clos_refl_trans R x y.
Proof. intros H. exists 1%nat. exists y. split; [exact H|reflexivity]. Qed.
Lemma magic_rt_map__maximum_revenue {A B : Type}
    (R : A -> A -> Prop) (S : B -> B -> Prop) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, SetsClass.RelsDomain.clos_refl_trans R x y ->
    SetsClass.RelsDomain.clos_refl_trans S (f x) (f y).
Proof.
  intros Hstep x y [n Hn]. exists n. revert x y Hn.
  induction n as [|n IH]; intros x y Hn.
  - change (x = y) in Hn. subst. reflexivity.
  - destruct Hn as [z [Hx Hz]]. exists (f z). split.
    + exact (Hstep x z Hx).
    + exact (IH z y Hz).
Qed.
Lemma magic_trade_lift__maximum_revenue c a b av bv h delta x y :
  0 <= delta -> MagicTrade c a b x y ->
  MagicTrade c (av :: a) (bv :: b)
    (let '(cash,(scrolls,items)) := x in (cash+delta,(scrolls,h::items)))
    (let '(cash,(scrolls,items)) := y in (cash+delta,(scrolls,h::items))).
Proof.
  intros Hd H. destruct x as [cash [sc it]], y as [cash' [sc' it']].
  unfold MagicTrade in *. simpl in *.
  destruct H as [[Hc He]|[[i [Hi [Hz [Hab [Hs He]]]]]|[i [Hi Hsale]]]].
  - inversion He; subst. left. split; [lia|]. f_equal; lia.
  - inversion He; subst. right; left. exists (i+1).
    rewrite Zlength_cons. rewrite !Znth_cons by lia.
    replace (i+1-1) with i by lia.
    rewrite replace_Znth_cons by lia.
    replace (i+1-1) with i by lia. repeat split; auto; lia.
  - right; right. exists (i+1). rewrite Zlength_cons.
    split; [lia|]. rewrite !Znth_cons by lia.
    replace (i+1-1) with i by lia.
    rewrite replace_Znth_cons by lia.
    replace (i+1-1) with i by lia.
    destruct Hsale as [[Hz He]|[Hz He]]; inversion He; subst.
    + left. split; auto. f_equal; lia.
    + right. split; auto. f_equal; lia.
Qed.
Lemma magic_all_raw__maximum_revenue c a b :
  Forall (Z.le 0) a -> length a = length b ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (0,(0,map (fun _ : Z => 0) a))
    (ListLib.sum a,(0,map (fun _ : Z => 2) a)).
Proof.
  revert b. induction a as [|av a IH]; intros b Ha Hl.
  - destruct b; [reflexivity|discriminate].
  - destruct b as [|bv b]; [discriminate|].
    inversion Ha; subst. simpl in Hl. injection Hl as Hl.
    specialize (IH b H2 Hl).
    pose proof (magic_rt_map__maximum_revenue
      (MagicTrade c a b) (MagicTrade c (av::a) (bv::b))
      (fun x => let '(cash,(sc,it)) := x in (cash+av,(sc,2::it)))
      (fun x y H => magic_trade_lift__maximum_revenue c a b av bv 2 av x y H1 H)
      _ _ IH) as Hlift.
    simpl in Hlift.
    change (SetsClass.RelsDomain.clos_refl_trans (MagicTrade c (av::a) (bv::b))
      (0,(0,0::map (fun _ : Z => 0) a))
      (av + ListLib.sum a,(0,2::map (fun _ : Z => 2) a))).
    replace (av + ListLib.sum a) with (ListLib.sum a + av) by lia.
    eapply SetsClass.RelsDomain.rt2_trans_ins; [|exact Hlift].
    apply magic_rt_step__maximum_revenue. unfold MagicTrade.
    right; right. exists 0. rewrite Zlength_cons.
    split; [pose proof (Zlength_nonneg a); lia|].
    left. split; reflexivity.
Qed.
Lemma magic_sum_change__maximum_revenue n i (f g : Z -> Z) :
  0 <= i < n ->
  (forall j, 0 <= j < n -> i <> j -> f j = g j) ->
  Sum.sum (fun j => 0 <= j < n) f =
    Sum.sum (fun j => 0 <= j < n) g + f i - g i.
Proof.
  intros Hi He.
  rewrite (sum_Z_range_split 0 i n f) by lia.
  rewrite (sum_Z_range_split 0 i n g) by lia.
  rewrite (sum_Z_range_split i (i+1) n f) by lia.
  rewrite (sum_Z_range_split i (i+1) n g) by lia.
  rewrite !sum_Z_range_single.
  assert (Hleft : Sum.sum (fun j => 0 <= j < i) f =
    Sum.sum (fun j => 0 <= j < i) g).
  { apply sum_Z_range_ext. intros j Hj. apply He; lia. }
  assert (Hright : Sum.sum (fun j => i+1 <= j < n) f =
    Sum.sum (fun j => i+1 <= j < n) g).
  { apply sum_Z_range_ext. intros j Hj. apply He; lia. }
  lia.
Qed.
Lemma magic_sum_replace__maximum_revenue (f : Z -> Z -> Z) items i v :
  0 <= i < Zlength items ->
  Sum.sum (fun j => 0 <= j < Zlength items)
    (fun j => f j (Znth j (replace_Znth i v items) 0)) =
  Sum.sum (fun j => 0 <= j < Zlength items)
    (fun j => f j (Znth j items 0)) + f i v - f i (Znth i items 0).
Proof.
  intros Hi. rewrite (magic_sum_change__maximum_revenue _ i
    (fun j => f j (Znth j (replace_Znth i v items) 0))
    (fun j => f j (Znth j items 0))) by
    (auto; intros; rewrite Znth_replace_Znth_Diff; auto).
  rewrite Znth_replace_Znth_Same by auto. reflexivity.
Qed.
Lemma magic_map_const_nth__maximum_revenue (a : list Z) v i :
  0 <= i < Zlength a -> Znth i (map (fun _ : Z => v) a) 0 = v.
Proof.
  intros Hi. unfold Znth.
  rewrite (nth_indep (map (fun _ : Z => v) a) 0 v) by
    (rewrite length_map; rewrite Zlength_correct in Hi; lia).
  exact (map_nth (fun _ : Z => v) a 0 (Z.to_nat i)).
Qed.
Lemma magic_no_capital_bound__maximum_revenue c a b cash sc items :
  Forall (Z.le 0) a -> ListLib.sum a < c ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (0,(0,map (fun _ : Z => 0) a)) (cash,(sc,items)) ->
  cash <= ListLib.sum a.
Proof.
  intros Ha Hc Hrt.
  set (f := fun i st => if Z.eqb st 0 then Znth i a 0 else 0).
  set (rem := fun it => Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => f i (Znth i it 0))).
  assert (Hnonneg : forall it, 0 <= rem it).
  { intros it. unfold rem, f.
    rewrite <- (sum_Z_range_zero 0 (Zlength a)) at 1.
    apply sum_Z_range_le. intros j Hj.
    destruct (Z.eqb (Znth j it 0) 0); [|lia].
    eapply Forall_Znth_Zlength; eauto. }
  set (P := fun x : Z * (Z * list Z) =>
    let '(xv,(xs,xi)) := x in
    Zlength xi = Zlength a /\ xs = 0 /\
    (forall i, 0 <= i < Zlength a -> Znth i xi 0 = 0 \/ Znth i xi 0 = 2) /\
    xv + rem xi <= ListLib.sum a).
  assert (Hinit : P (0,(0,map (fun _ : Z => 0) a))).
  { unfold P. repeat split.
    - rewrite !Zlength_correct, length_map. reflexivity.
    - intros i Hi. left. apply magic_map_const_nth__maximum_revenue; auto.
    - unfold rem. rewrite (sum_Z_range_ext 0 (Zlength a) _ (fun i => Znth i a 0)).
      + rewrite <- list_sum_as_Z_range_sum. lia.
      + intros i Hi. rewrite magic_map_const_nth__maximum_revenue by auto.
        unfold f. reflexivity. }
  assert (Hstep : forall x y, P x -> MagicTrade c a b x y -> P y).
  { intros [xv [xs xi]] [yv [ys yi]] HP HT.
    destruct HP as [Hl [Hs [Hst Hv]]].
    unfold MagicTrade in HT.
    destruct HT as [[Hbuy He]|[[i [Hi [Hz [Hab [Hscroll He]]]]]|[i [Hi Hsale]]]].
    - pose proof (Hnonneg xi). lia.
    - lia.
    - destruct Hsale as [[Hz He]|[Hz He]].
      + inversion He; subst. unfold P. rewrite Zlength_replace_Znth.
        split; [exact Hl|]. split; [reflexivity|]. split.
        * intros j Hj. destruct (Z.eq_dec i j) as [->|Hij].
          -- right. rewrite Znth_replace_Znth_Same; lia.
          -- rewrite Znth_replace_Znth_Diff; auto; lia.
        * assert (Hr : rem (replace_Znth i 2 xi) = rem xi - Znth i a 0).
          { unfold rem. rewrite <- Hl.
            rewrite magic_sum_replace__maximum_revenue by lia.
            rewrite Hl, Hz. unfold f. simpl. lia. }
          rewrite Hr. lia.
      + specialize (Hst i Hi). lia. }
  pose proof (magic_rt_invariant__maximum_revenue _ P Hstep _ _ Hrt Hinit) as Hfinal.
  change (Zlength items = Zlength a /\ sc = 0 /\
    (forall i, 0 <= i < Zlength a -> Znth i items 0 = 0 \/ Znth i items 0 = 2) /\
    cash + rem items <= ListLib.sum a) in Hfinal.
  pose proof (Hnonneg items). tauto || lia.
Qed.
Lemma magic_no_capital_optimum__maximum_revenue c a b :
  Forall (Z.le 0) a -> length a = length b -> ListLib.sum a < c ->
  MaximumMagicRevenue c a b (ListLib.sum a).
Proof.
  intros Ha Hl Hc. unfold MaximumMagicRevenue, max_value_of_subset,
    max_object_of_subset.
  exists (ListLib.sum a). split; [split|reflexivity].
  - exists 0, (map (fun _ : Z => 2) a). split.
    + apply magic_all_raw__maximum_revenue; auto.
    + apply Forall_map. apply Forall_forall. intros. reflexivity.
  - intros cash [sc [items [Hrt Hall]]].
    eapply magic_no_capital_bound__maximum_revenue; eauto.
Qed.
Lemma magic_unconstrained_bound__maximum_revenue c a b cash sc items :
  0 <= c -> Zlength a = Zlength b ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (0,(0,map (fun _ : Z => 0) a)) (cash,(sc,items)) ->
  Forall (eq 2) items -> cash <= UnconstrainedRevenue c a b.
Proof.
  intros Hc Hab Hrt Hall.
  set (f := fun i st => if Z.eqb st 0 then Z.max (Znth i a 0) (Znth i b 0-c)
    else if Z.eqb st 1 then Znth i b 0 else 0).
  set (rem := fun it => Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => f i (Znth i it 0))).
  set (P := fun x : Z * (Z * list Z) =>
    let '(xv,(xs,xi)) := x in
    Zlength xi = Zlength a /\ 0 <= xs /\
    xv + c*xs + rem xi <= UnconstrainedRevenue c a b).
  assert (Hinit : P (0,(0,map (fun _ : Z => 0) a))).
  { unfold P. split.
    - rewrite !Zlength_correct, length_map. reflexivity.
    - split; [lia|]. unfold rem, UnconstrainedRevenue.
      rewrite (list_sum_map_combine_as_Z_range_sum 0 0
        (fun av bv => Z.max av (bv-c)) a b).
      rewrite <- Hab, Z.min_id.
      rewrite (sum_Z_range_ext 0 (Zlength a)
        (fun i => f i (Znth i (map (fun _ : Z => 0) a) 0))
        (fun i => Z.max (Znth i a 0) (Znth i b 0-c))).
      + lia.
      + intros i Hi. rewrite magic_map_const_nth__maximum_revenue by auto.
        unfold f. reflexivity. }
  assert (Hstep : forall x y, P x -> MagicTrade c a b x y -> P y).
  { intros [xv [xs xi]] [yv [ys yi]] [Hl [Hs Hv]] HT.
    unfold MagicTrade in HT.
    assert (Hupd : forall i v, 0 <= i < Zlength a ->
      rem (replace_Znth i v xi) = rem xi + f i v - f i (Znth i xi 0)).
    { intros i v Hi. unfold rem. rewrite <- Hl.
      apply magic_sum_replace__maximum_revenue. lia. }
    destruct HT as [[Hbuy He]|[[i [Hi [Hz [Hprice [Hscroll He]]]]]|[i [Hi Hsale]]]].
    - inversion He; subst. unfold P. repeat split; auto; nia.
    - inversion He; subst. unfold P. rewrite Zlength_replace_Znth.
      split; [auto|]. split; [lia|]. rewrite Hupd by auto.
      rewrite Hz. unfold f. simpl.
      pose proof (Z.le_max_r (Znth i a 0) (Znth i b 0-c)). nia.
    - destruct Hsale as [[Hz He]|[Hz He]]; inversion He; subst;
        unfold P; rewrite Zlength_replace_Znth;
        (split; [auto|split; [auto|]]); rewrite Hupd by auto;
        rewrite Hz; unfold f; simpl.
      + pose proof (Z.le_max_l (Znth i a 0) (Znth i b 0-c)). nia.
      + nia. }
  pose proof (magic_rt_invariant__maximum_revenue _ P Hstep _ _ Hrt Hinit) as HP.
  destruct HP as [Hl [Hs Hv]].
  assert (Hr : rem items = 0).
  { unfold rem. apply sum_Z_range_eq_zero. intros i Hi.
    assert (Hz : 2 = Znth i items 0).
    { eapply Forall_Znth_Zlength; [exact Hall|lia]. }
    rewrite <- Hz. unfold f. reflexivity. }
  rewrite Hr in Hv. nia.
Qed.
Lemma magic_raw_subset__maximum_revenue c a b pick :
  Forall (Z.le 0) a -> length a = length b -> length a = length pick ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (0,(0,map (fun _ : Z => 0) a))
    (ListLib.sum (map (fun p : Z * bool => if snd p then fst p else 0)
      (combine a pick)),(0,map (fun p : bool => if p then 2 else 0) pick)).
Proof.
  revert b pick. induction a as [|av a IH]; intros b pick Ha Hlen Hp.
  - destruct b, pick; try discriminate. reflexivity.
  - destruct b as [|bv b], pick as [|p pick]; try discriminate.
    inversion Ha as [|? ? Hav Hat]; subst.
    simpl in Hlen, Hp. injection Hlen as Hlen. injection Hp as Hp.
    specialize (IH b pick Hat Hlen Hp). destruct p; simpl.
    + pose proof (magic_rt_map__maximum_revenue
        (MagicTrade c a b) (MagicTrade c (av::a) (bv::b))
        (fun x => let '(cash,(sc,it)) := x in (cash+av,(sc,2::it)))
        (fun x y H => magic_trade_lift__maximum_revenue c a b av bv 2 av x y Hav H)
        _ _ IH) as Hlift.
      simpl in Hlift. rewrite Z.add_comm.
      eapply SetsClass.RelsDomain.rt2_trans_ins; [|exact Hlift].
      apply magic_rt_step__maximum_revenue. unfold MagicTrade.
      right; right. exists 0. rewrite Zlength_cons.
      split; [pose proof (Zlength_nonneg a); lia|]. left. split; reflexivity.
    + pose proof (magic_rt_map__maximum_revenue
        (MagicTrade c a b) (MagicTrade c (av::a) (bv::b))
        (fun x => let '(cash,(sc,it)) := x in (cash+0,(sc,0::it)))
        (fun x y H => magic_trade_lift__maximum_revenue c a b av bv 0 0 x y (Z.le_refl 0) H)
        _ _ IH) as Hlift.
      simpl in Hlift. rewrite Z.add_0_r in Hlift. exact Hlift.
Qed.
Lemma magic_identify_head__maximum_revenue c av bv a b cash items :
  c <= cash -> av < bv ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c (av::a) (bv::b))
    (cash,(0,0::items)) (cash+bv-c,(0,2::items)).
Proof.
  intros Hc Hab.
  eapply SetsClass.RelsDomain.rt2_trans_ins with
    (y := (cash-c,(1,0::items))).
  - apply magic_rt_step__maximum_revenue. unfold MagicTrade.
    left. split; auto.
  - eapply SetsClass.RelsDomain.rt2_trans_ins with
      (y := (cash-c,(0,1::items))).
    + apply magic_rt_step__maximum_revenue. unfold MagicTrade.
      right; left. exists 0. rewrite Zlength_cons.
      repeat split; try assumption; try reflexivity;
        pose proof (Zlength_nonneg a); lia.
    + apply magic_rt_step__maximum_revenue. unfold MagicTrade.
      right; right. exists 0. rewrite Zlength_cons.
      split; [pose proof (Zlength_nonneg a); lia|].
      right. split; [reflexivity|].
      replace (cash+bv-c) with (cash-c+bv) by lia. reflexivity.
Qed.
Lemma magic_finish_profitable__maximum_revenue c a b items cash :
  length a = length b -> c <= cash ->
  Forall2 (fun p st => st = 2 \/
    (st = 0 /\ fst p < snd p /\ c <= snd p)) (combine a b) items ->
  SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (cash,(0,items))
    (cash + ListLib.sum (map (fun p : Z * Z => if Z.eqb (snd p) 0 then fst p-c else 0)
      (combine b items)),(0,map (fun _ : Z => 2) a)).
Proof.
  revert b items cash. induction a as [|av a IH]; intros b items cash Hlen Hc Hstates.
  - destruct b; [|discriminate]. inversion Hstates; subst. simpl.
    rewrite Z.add_0_r. reflexivity.
  - destruct b as [|bv b]; [discriminate|].
    inversion Hstates as [|p st ps its Hst Htail]; subst.
    simpl in Hlen. injection Hlen as Hlen. simpl in Hst.
    destruct Hst as [->|[-> [Hab Hb]]].
    + specialize (IH b its cash Hlen Hc Htail).
      pose proof (magic_rt_map__maximum_revenue
        (MagicTrade c a b) (MagicTrade c (av::a) (bv::b))
        (fun x => let '(v,(sc,it)) := x in (v+0,(sc,2::it)))
        (fun x y H => magic_trade_lift__maximum_revenue c a b av bv 2 0 x y (Z.le_refl 0) H)
        _ _ IH) as Hlift.
      simpl in *. rewrite !Z.add_0_r in Hlift. exact Hlift.
    + specialize (IH b its (cash+bv-c) Hlen ltac:(lia) Htail).
      pose proof (magic_rt_map__maximum_revenue
        (MagicTrade c a b) (MagicTrade c (av::a) (bv::b))
        (fun x => let '(v,(sc,it)) := x in (v+0,(sc,2::it)))
        (fun x y H => magic_trade_lift__maximum_revenue c a b av bv 2 0 x y (Z.le_refl 0) H)
        _ _ IH) as Hlift.
      simpl in *. rewrite !Z.add_0_r in Hlift.
      replace (cash + (bv-c + ListLib.sum
        (map (fun p : Z * Z => if snd p =? 0 then fst p-c else 0) (combine b its))))
        with (cash+bv-c + ListLib.sum
        (map (fun p : Z * Z => if snd p =? 0 then fst p-c else 0) (combine b its))) by lia.
      eapply SetsClass.RelsDomain.rt2_trans_ins; [|exact Hlift].
      apply magic_identify_head__maximum_revenue; auto.
Qed.
Lemma magic_free_bookkeeping__maximum_revenue c a b :
  0 <= c -> Forall (Z.le 1) a -> Forall2 Z.le a b ->
  let pick := map (fun p : Z * Z => Z.leb (snd p-fst p-c) 0) (combine a b) in
  length a = length b /\ length a = length pick /\
  Forall2 (fun p st => st = 2 \/
    (st = 0 /\ fst p < snd p /\ c <= snd p))
    (combine a b) (map (fun p : bool => if p then 2 else 0) pick) /\
  ListLib.sum (map (fun p : Z * bool => if snd p then fst p else 0)
    (combine a pick)) = FreeCash c a b /\
  FreeCash c a b + ListLib.sum (map
    (fun p : Z * Z => if Z.eqb (snd p) 0 then fst p-c else 0)
    (combine b (map (fun p : bool => if p then 2 else 0) pick))) =
    UnconstrainedRevenue c a b.
Proof.
  intros Hc Ha Hab. induction Hab as [|av bv a b Hav Hab IH].
  - simpl. repeat split; try reflexivity. constructor.
  - inversion Ha as [|? ? Ha0 Hat]; subst. specialize (IH Hat).
    cbn zeta in *. destruct IH as [Hl [Hp [Hstates [Hcash Hsum]]]].
    unfold FreeCash, UnconstrainedRevenue in *. simpl in *.
    destruct (Z.leb (bv-av-c) 0) eqn:He; simpl.
    + apply Z.leb_le in He. rewrite Z.max_l by lia.
      repeat split; try lia.
      constructor; auto.
    + apply Z.leb_gt in He. rewrite Z.max_r by lia.
      repeat split; try lia.
      constructor; auto. right. simpl. repeat split; lia.
Qed.
Lemma magic_free_optimum__maximum_revenue c a b :
  0 <= c -> Forall (Z.le 1) a -> Forall2 Z.le a b ->
  c <= FreeCash c a b -> MaximumMagicRevenue c a b (UnconstrainedRevenue c a b).
Proof.
  intros Hc Ha Hab Hfree.
  pose proof (magic_free_bookkeeping__maximum_revenue c a b Hc Ha Hab) as Hbook.
  cbn zeta in Hbook.
  set (pick := map (fun p : Z * Z => Z.leb (snd p-fst p-c) 0) (combine a b)) in *.
  destruct Hbook as [Hl [Hp [Hstates [Hcash Hsum]]]].
  assert (Ha0 : Forall (Z.le 0) a).
  { eapply Forall_impl; [|exact Ha]. intros z Hz. lia. }
  pose proof (magic_raw_subset__maximum_revenue c a b pick Ha0 Hl Hp) as Hraw.
  rewrite Hcash in Hraw.
  pose proof (magic_finish_profitable__maximum_revenue c a b
    (map (fun p : bool => if p then 2 else 0) pick) (FreeCash c a b)
    Hl Hfree Hstates) as Hfinish.
  rewrite Hsum in Hfinish.
  unfold MaximumMagicRevenue, max_value_of_subset, max_object_of_subset.
  exists (UnconstrainedRevenue c a b). split; [split|reflexivity].
  - exists 0, (map (fun _ : Z => 2) a). split.
    + eapply SetsClass.RelsDomain.rt2_trans_ins; eauto.
    + apply Forall_map, Forall_forall. intros. reflexivity.
  - intros cash [sc [items [Hrt Hall]]].
    eapply magic_unconstrained_bound__maximum_revenue; eauto.
    rewrite !Zlength_correct, Hl. reflexivity.
Qed.
Lemma magic_sum_selected__maximum_revenue lo hi (S : Z -> Prop) f :
  Sum.sum (fun i => lo <= i < hi /\ S i) f =
  Sum.sum (fun i => lo <= i < hi) (fun i => if Sum.prop_dec (S i) then f i else 0).
Proof.
  unfold Sum.sum, finite_Z_range', finite_Z_range. simpl.
  induction (Zrange lo hi) as [|x xs IH]; simpl; [reflexivity|].
  destruct (Sum.prop_dec (S x)); simpl; rewrite IH; lia.
Qed.
Lemma magic_Znth_map__maximum_revenue {A B : Type} (f : A -> B) a da db i :
  0 <= i < Zlength a -> Znth i (map f a) db = f (Znth i a da).
Proof.
  intros Hi. unfold Znth.
  rewrite (nth_indep (map f a) db (f da)) by
    (rewrite length_map; rewrite Zlength_correct in Hi; lia).
  apply map_nth.
Qed.
Lemma magic_bool_list__maximum_revenue (f : Z -> bool) n :
  exists pick : list bool, length pick = n /\
    forall i, 0 <= i < Z.of_nat n -> Znth i pick false = f i.
Proof.
  revert f. induction n as [|n IH]; intros f.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - destruct (IH (fun i => f (i+1))) as [pick [Hl Hnth]].
    exists (f 0 :: pick). split; [simpl; lia|]. intros i Hi.
    destruct (Z.eq_dec i 0) as [->|Hne]; [reflexivity|].
    rewrite Znth_cons by lia. rewrite Hnth by lia.
    f_equal. lia.
Qed.
Lemma magic_Forall2_Znth__maximum_revenue {A B : Type} (P : A -> B -> Prop)
    a b da db :
  Zlength a = Zlength b ->
  (forall i, 0 <= i < Zlength a -> P (Znth i a da) (Znth i b db)) ->
  Forall2 P a b.
Proof.
  revert b. induction a as [|x a IH]; intros b Hl Hp.
  - destruct b as [|y b]; [apply Forall2_nil|rewrite Zlength_nil, Zlength_cons in Hl;
      pose proof (Zlength_nonneg b); lia].
  - destruct b as [|y b]; [rewrite Zlength_nil, Zlength_cons in Hl;
      pose proof (Zlength_nonneg a); lia|].
    constructor.
    + apply (Hp 0). rewrite Zlength_cons. pose proof (Zlength_nonneg a). lia.
    + apply IH; [rewrite !Zlength_cons in Hl; lia|]. intros i Hi.
      specialize (Hp (i+1)). rewrite !Znth_cons in Hp by lia.
      replace (i+1-1) with i in Hp by lia. apply Hp.
      rewrite Zlength_cons. lia.
Qed.
Lemma magic_selected_schedule__maximum_revenue c a b (S : Z -> Prop) :
  0 <= c -> Forall (Z.le 1) a -> Forall2 Z.le a b ->
  (forall i, 0 <= i < Zlength a -> S i -> 0 < Znth i b 0-Znth i a 0-c) ->
  c <= FreeCash c a b + Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i a 0) ->
  exists sc items,
    SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
      (0,(0,map (fun _ : Z => 0) a))
      (UnconstrainedRevenue c a b -
        Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i b 0-Znth i a 0-c),
        (sc,items)) /\ Forall (eq 2) items.
Proof.
  intros Hc Ha Hab HS Hcash.
  destruct (proj1 (Forall2_nth_iff Z Z Z.le a b 0 0) Hab) as [Hlen Hnth].
  assert (HlenZ : Zlength b = Zlength a) by (rewrite !Zlength_correct, Hlen; reflexivity).
  set (choose := fun i => if Z.leb (Znth i b 0-Znth i a 0-c) 0 then true
    else if Sum.prop_dec (S i) then true else false).
  destruct (magic_bool_list__maximum_revenue choose (length a)) as [pick [Hplen Hpick]].
  assert (HplenZ : Zlength pick = Zlength a) by (rewrite !Zlength_correct, Hplen; reflexivity).
  assert (HpickZ : forall i, 0 <= i < Zlength a -> Znth i pick false = choose i).
  { intros. apply Hpick. rewrite <- Zlength_correct. auto. }
  set (states := map (fun p : bool => if p then 2 else 0) pick).
  assert (Hstlen : Zlength states = Zlength a).
  { unfold states. rewrite !Zlength_correct, length_map, Hplen. reflexivity. }
  assert (Hstnth : forall i, 0 <= i < Zlength a ->
    Znth i states 0 = if choose i then 2 else 0).
  { intros i Hi. unfold states. rewrite (magic_Znth_map__maximum_revenue _ _ false 0 i) by lia.
    rewrite HpickZ by auto. reflexivity. }
  assert (Hstates : Forall2 (fun p st => st = 2 \/
      (st = 0 /\ fst p < snd p /\ c <= snd p)) (combine a b) states).
  { apply (magic_Forall2_Znth__maximum_revenue _ _ _ (0,0) 0).
    - rewrite Zlength_correct, length_combine, <- Hlen, Nat.min_id.
      rewrite Hstlen, Zlength_correct. reflexivity.
    - intros i Hi.
      assert (Hi' : 0 <= i < Zlength a).
      { rewrite Zlength_correct, length_combine, <- Hlen, Nat.min_id in Hi.
        rewrite Zlength_correct. exact Hi. }
      rewrite Hstnth by auto. unfold Znth. rewrite !combine_nth by auto. simpl.
      unfold choose. destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0) eqn:He.
      + left. reflexivity.
      + destruct (Sum.prop_dec (S i)); [left; reflexivity|]. right.
        apply Z.leb_gt in He.
        pose proof (@Forall_Znth_Zlength Z (Z.le 1) a 0 i Ha Hi') as Hpos.
        simpl. repeat split; auto; unfold Znth in *; lia. }
  set (raw := ListLib.sum (map (fun p : Z * bool => if snd p then fst p else 0) (combine a pick))).
  set (gain := ListLib.sum (map (fun p : Z * Z => if Z.eqb (snd p) 0 then fst p-c else 0)
    (combine b states))).
  assert (Hraw : raw = FreeCash c a b +
    Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i a 0)).
  { unfold raw, FreeCash. rewrite magic_sum_selected__maximum_revenue.
    rewrite (list_sum_map_combine_as_Z_range_sum 0 false (fun av p => if p then av else 0) a pick).
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => if Z.leb (bv-av-c) 0 then av else 0) a b).
    rewrite HplenZ, HlenZ, !Z.min_id, <- sum_Z_range_add.
    apply sum_Z_range_ext. intros i Hi. rewrite HpickZ by auto.
    unfold choose. destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0) eqn:He;
      destruct (Sum.prop_dec (S i)); simpl; try lia.
    apply Z.leb_le in He. specialize (HS i Hi s). lia. }
  assert (Htotal : raw + gain = UnconstrainedRevenue c a b -
    Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i b 0-Znth i a 0-c)).
  { unfold raw, gain, UnconstrainedRevenue. rewrite magic_sum_selected__maximum_revenue.
    rewrite (list_sum_map_combine_as_Z_range_sum 0 false (fun av p => if p then av else 0) a pick).
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun bv st => if Z.eqb st 0 then bv-c else 0) b states).
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => Z.max av (bv-c)) a b).
    rewrite HplenZ, HlenZ, Hstlen, !Z.min_id.
    rewrite <- sum_Z_range_add, <- sum_Z_range_sub.
    apply sum_Z_range_ext. intros i Hi. rewrite HpickZ, Hstnth by auto.
    unfold choose. destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0) eqn:He.
    - apply Z.leb_le in He. rewrite Z.max_l by lia.
      destruct (Sum.prop_dec (S i)); simpl; [specialize (HS i Hi s)|]; lia.
    - apply Z.leb_gt in He. rewrite Z.max_r by lia.
      destruct (Sum.prop_dec (S i)); simpl; lia. }
  assert (Ha0 : Forall (Z.le 0) a).
  { eapply Forall_impl; [|exact Ha]. intros z Hz. lia. }
  pose proof (magic_raw_subset__maximum_revenue c a b pick Ha0 Hlen (eq_sym Hplen)) as Hrawrt.
  change (SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (0,(0,map (fun _ : Z => 0) a)) (raw,(0,states))) in Hrawrt.
  pose proof (magic_finish_profitable__maximum_revenue c a b states raw Hlen ltac:(lia) Hstates) as Hfinish.
  change (SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
    (raw,(0,states)) (raw+gain,(0,map (fun _ : Z => 2) a))) in Hfinish.
  rewrite Htotal in Hfinish. exists 0, (map (fun _ : Z => 2) a). split.
  - eapply SetsClass.RelsDomain.rt2_trans_ins; eauto.
  - apply Forall_map, Forall_forall. intros. reflexivity.
Qed.
Lemma magic_potential_step__maximum_revenue c a b :
  let f := fun i st => if Z.eqb st 0 then Z.max (Znth i a 0) (Znth i b 0-c)
    else if Z.eqb st 1 then Znth i b 0 else 0 in
  let rem := fun it => Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => f i (Znth i it 0)) in
  forall xv xs xi yv ys yi,
    Zlength xi = Zlength a -> 0 <= xs ->
    MagicTrade c a b (xv,(xs,xi)) (yv,(ys,yi)) ->
    Zlength yi = Zlength a /\ 0 <= ys /\
    yv + c*ys + rem yi <= xv + c*xs + rem xi.
Proof.
  intros f rem xv xs xi yv ys yi Hl Hs HT.
  assert (Hupd : forall i v, 0 <= i < Zlength a ->
    rem (replace_Znth i v xi) = rem xi + f i v - f i (Znth i xi 0)).
  { intros i v Hi. unfold rem. rewrite <- Hl.
    apply magic_sum_replace__maximum_revenue. lia. }
  unfold MagicTrade in HT.
  destruct HT as [[Hbuy He]|[[i [Hi [Hz [Hprice [Hscroll He]]]]]|[i [Hi Hsale]]]].
  - inversion He; subst. repeat split; auto; nia.
  - inversion He; subst. rewrite Zlength_replace_Znth.
    split; [auto|]. split; [lia|]. rewrite Hupd by auto.
    rewrite Hz. unfold f. simpl.
    pose proof (Z.le_max_r (Znth i a 0) (Znth i b 0-c)). nia.
  - destruct Hsale as [[Hz He]|[Hz He]]; inversion He; subst;
      rewrite Zlength_replace_Znth;
      (split; [auto|split; [auto|]]); rewrite Hupd by auto;
      rewrite Hz; unfold f; simpl.
    + pose proof (Z.le_max_l (Znth i a 0) (Znth i b 0-c)). nia.
    + nia.
Qed.
Lemma magic_first_purchase_bound__maximum_revenue c a b B :
  let f := fun i st => if Z.eqb st 0 then Z.max (Znth i a 0) (Znth i b 0-c)
    else if Z.eqb st 1 then Znth i b 0 else 0 in
  let rem := fun it => Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => f i (Znth i it 0)) in
  let raw := fun it => Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => if Z.eqb (Znth i it 0) 0 then Znth i a 0 else 0) in
  0 <= c -> ListLib.sum a <= B ->
  (forall cash it, Zlength it = Zlength a ->
    (forall i, 0 <= i < Zlength a -> Znth i it 0 = 0 \/ Znth i it 0 = 2) ->
    cash + raw it = ListLib.sum a -> c <= cash -> cash + rem it <= B) ->
  forall cash sc items,
    SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
      (0,(0,map (fun _ : Z => 0) a)) (cash,(sc,items)) ->
    Forall (eq 2) items -> cash <= B.
Proof.
  intros f rem raw Hc Hallraw Hbudget cash sc items Hrt Hall.
  set (P := fun x : Z * (Z * list Z) =>
    let '(xv,(xs,xi)) := x in Zlength xi = Zlength a /\ 0 <= xs /\
      ((xs = 0 /\
        (forall i, 0 <= i < Zlength a -> Znth i xi 0 = 0 \/ Znth i xi 0 = 2) /\
        xv + raw xi = ListLib.sum a) \/ xv + c*xs + rem xi <= B)).
  assert (Hinit : P (0,(0,map (fun _ : Z => 0) a))).
  { unfold P. split.
    - rewrite !Zlength_correct, length_map. reflexivity.
    - split; [lia|]. left. split; [reflexivity|]. split.
      + intros i Hi. left. apply magic_map_const_nth__maximum_revenue; auto.
      + unfold raw. rewrite (sum_Z_range_ext 0 (Zlength a) _ (fun i => Znth i a 0)).
        * rewrite <- list_sum_as_Z_range_sum. lia.
        * intros i Hi. rewrite magic_map_const_nth__maximum_revenue by auto. reflexivity. }
  assert (Hstep : forall x y, P x -> MagicTrade c a b x y -> P y).
  { intros [xv [xs xi]] [yv [ys yi]] [Hl [Hsc HP]] HT.
    pose proof (magic_potential_step__maximum_revenue c a b xv xs xi yv ys yi Hl Hsc HT)
      as [Hyl [Hys Hmono]].
    change (yv+c*ys+rem yi <= xv+c*xs+rem xi) in Hmono.
    unfold P. split; [exact Hyl|]. split; [exact Hys|].
    destruct HP as [[Hs [Hst Hraw]]|Hbound]; [|right; lia].
    unfold MagicTrade in HT.
    destruct HT as [[Hbuy He]|[[i [Hi [Hz [Hprice [Hscroll He]]]]]|[i [Hi Hsale]]]].
    - right. specialize (Hbudget xv xi Hl Hst Hraw Hbuy). subst xs. lia.
    - lia.
    - destruct Hsale as [[Hz He]|[Hz He]].
      + inversion He; subst. left. split; [reflexivity|]. split.
        * intros j Hj. destruct (Z.eq_dec i j) as [->|Hij].
          -- right. rewrite Znth_replace_Znth_Same; lia.
          -- rewrite Znth_replace_Znth_Diff; auto; lia.
        * unfold raw in *. rewrite <- Hl.
          rewrite (magic_sum_replace__maximum_revenue
            (fun i st => if Z.eqb st 0 then Znth i a 0 else 0) xi i 2) by lia.
          rewrite Hl, Hz. simpl. lia.
      + specialize (Hst i Hi). lia. }
  pose proof (magic_rt_invariant__maximum_revenue _ P Hstep _ _ Hrt Hinit) as HP.
  destruct HP as [Hl [Hs [Hraw|Hbound]]].
  - assert (Hz : raw items = 0).
    { unfold raw. apply sum_Z_range_eq_zero. intros i Hi.
      assert (Htwo : 2 = Znth i items 0) by (eapply Forall_Znth_Zlength; [exact Hall|lia]).
      rewrite <- Htwo. reflexivity. }
    destruct Hraw as [_ [_ Hraw]]. rewrite Hz in Hraw. lia.
  - assert (Hz : rem items = 0).
    { unfold rem. apply sum_Z_range_eq_zero. intros i Hi.
      assert (Htwo : 2 = Znth i items 0) by (eapply Forall_Znth_Zlength; [exact Hall|lia]).
      rewrite <- Htwo. unfold f. reflexivity. }
    rewrite Hz in Hbound. nia.
Qed.
Lemma magic_profit_totals__maximum_revenue c a b :
  1 <= c -> 1 <= Zlength a <= 1000 ->
  Forall (Z.le 1) a -> Forall2 Z.le a b -> Forall (Z.ge 10000) b ->
  let S := fun i => 0 < Znth i b 0-Znth i a 0-c in
  let cap := Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i a 0) in
  let loss := Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i b 0-Znth i a 0-c) in
  FreeCash c a b + cap = ListLib.sum a /\
  ListLib.sum a + loss = UnconstrainedRevenue c a b /\ loss < 10000001.
Proof.
  intros Hc Hn Ha Hab Hb S cap loss.
  assert (Hl : Zlength b = Zlength a).
  { rewrite !Zlength_correct, (Forall2_length Hab). reflexivity. }
  split.
  - unfold cap, FreeCash. rewrite magic_sum_selected__maximum_revenue.
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => if Z.leb (bv-av-c) 0 then av else 0) a b), Hl, Z.min_id.
    rewrite list_sum_as_Z_range_sum, <- sum_Z_range_add.
    apply sum_Z_range_ext. intros i Hi. unfold S.
    destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0) eqn:He;
      destruct (Sum.prop_dec (0 < Znth i b 0-Znth i a 0-c));
      [apply Z.leb_le in He| | |apply Z.leb_gt in He]; lia.
  - split.
    + unfold loss, UnconstrainedRevenue. rewrite magic_sum_selected__maximum_revenue.
      rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => Z.max av (bv-c)) a b), Hl, Z.min_id.
      rewrite list_sum_as_Z_range_sum, <- sum_Z_range_add.
      apply sum_Z_range_ext. intros i Hi. unfold S.
      destruct (Sum.prop_dec (0 < Znth i b 0-Znth i a 0-c)).
      * rewrite Z.max_r by lia. lia.
      * rewrite Z.max_l by lia. lia.
    + assert (Hbound : loss <= (Zlength a-0)*10000).
      { unfold loss. rewrite magic_sum_selected__maximum_revenue.
        apply sum_Z_range_upper_bound; [lia|]. intros i Hi.
        unfold S. destruct (Sum.prop_dec (0 < Znth i b 0-Znth i a 0-c)); [|lia].
        pose proof (@Forall_Znth_Zlength Z (Z.le 1) a 0 i Ha Hi).
        pose proof (@Forall_Znth_Zlength Z (Z.ge 10000) b 0 i Hb ltac:(lia)).
        lia. }
      nia.
Qed.
Lemma magic_raw_capital_accounting__maximum_revenue c a b cash items :
  Forall (Z.le 0) a -> Zlength a = Zlength b -> Zlength items = Zlength a ->
  (forall i, 0 <= i < Zlength a -> Znth i items 0 = 0 \/ Znth i items 0 = 2) ->
  cash + Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => if Z.eqb (Znth i items 0) 0 then Znth i a 0 else 0) = ListLib.sum a ->
  let S := fun i => Znth i items 0 = 2 /\ 0 < Znth i b 0-Znth i a 0-c in
  let cap := Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i a 0) in
  let loss := Sum.sum (fun i => 0 <= i < Zlength a /\ S i) (fun i => Znth i b 0-Znth i a 0-c) in
  cash <= FreeCash c a b + cap /\
  cash + Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => if Z.eqb (Znth i items 0) 0 then Z.max (Znth i a 0) (Znth i b 0-c)
      else if Z.eqb (Znth i items 0) 1 then Znth i b 0 else 0) =
    UnconstrainedRevenue c a b-loss.
Proof.
  intros Ha Hab Hlen Hstates Hcash S cap loss.
  assert (Hsumcash : cash = Sum.sum (fun i => 0 <= i < Zlength a)
    (fun i => Znth i a 0 - (if Z.eqb (Znth i items 0) 0 then Znth i a 0 else 0))).
  { rewrite sum_Z_range_sub, <- list_sum_as_Z_range_sum. lia. }
  split.
  - rewrite Hsumcash. unfold cap, FreeCash. rewrite magic_sum_selected__maximum_revenue.
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => if Z.leb (bv-av-c) 0 then av else 0) a b), <- Hab, Z.min_id.
    rewrite <- sum_Z_range_add. apply sum_Z_range_le. intros i Hi.
    pose proof (@Forall_Znth_Zlength Z (Z.le 0) a 0 i Ha Hi) as Hpos.
    unfold S. destruct (Hstates i Hi) as [Hz|Hz]; rewrite Hz; simpl.
    + destruct (Sum.prop_dec (0 = 2 /\ 0 < Znth i b 0-Znth i a 0-c)); [lia|].
      destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0); lia.
    + destruct (Z.leb (Znth i b 0-Znth i a 0-c) 0) eqn:He;
        destruct (Sum.prop_dec (2 = 2 /\ 0 < Znth i b 0-Znth i a 0-c)) as [HS|HS];
        try (apply Z.leb_le in He); try (apply Z.leb_gt in He); lia.
  - rewrite Hsumcash. unfold loss, UnconstrainedRevenue. rewrite magic_sum_selected__maximum_revenue.
    rewrite (list_sum_map_combine_as_Z_range_sum 0 0 (fun av bv => Z.max av (bv-c)) a b), <- Hab, Z.min_id.
    rewrite <- sum_Z_range_add, <- sum_Z_range_sub. apply sum_Z_range_ext. intros i Hi.
    unfold S. destruct (Hstates i Hi) as [Hz|Hz]; rewrite Hz; simpl.
    + destruct (Sum.prop_dec (0 = 2 /\ 0 < Znth i b 0-Znth i a 0-c)); [lia|]. lia.
    + destruct (Sum.prop_dec (2 = 2 /\ 0 < Znth i b 0-Znth i a 0-c)) as [HS|HS].
      * rewrite Z.max_r by lia. lia.
      * rewrite Z.max_l by lia. lia.
Qed.
Lemma magic_capital_optimum__maximum_revenue c a b loss :
  1 <= c -> 1 <= Zlength a <= 1000 ->
  Forall (Z.le 1) a -> Forall2 Z.le a b -> Forall (Z.ge 10000) b ->
  c <= ListLib.sum a ->
  MinimumSacrifice c a b (Zlength a) (c-FreeCash c a b) loss ->
  MaximumMagicRevenue c a b (UnconstrainedRevenue c a b-loss).
Proof.
  intros Hc Hn Ha Hab Hb Hcapital Hminspec.
  pose proof (magic_profit_totals__maximum_revenue c a b Hc Hn Ha Hab Hb) as Htot.
  cbn zeta in Htot. destruct Htot as [Hcapall [Hlossall Hlossbound]].
  unfold MinimumSacrifice, min_value_of_subset, min_object_of_subset in Hminspec.
  destruct Hminspec as [v [[Hv Hmin] Heq]]. subst v.
  assert (Hminall : loss <= Sum.sum
    (fun i => 0 <= i < Zlength a /\ 0 < Znth i b 0-Znth i a 0-c)
    (fun i => Znth i b 0-Znth i a 0-c)).
  { apply Hmin. right. exists (fun i => 0 < Znth i b 0-Znth i a 0-c).
    split; [auto|]. split; [lia|reflexivity]. }
  assert (Hatt : exists sc items,
    SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
      (0,(0,map (fun _ : Z => 0) a))
      (UnconstrainedRevenue c a b-loss,(sc,items)) /\ Forall (eq 2) items).
  { destruct Hv as [Hinf|[S [HS [Hcap Hloss]]]]; [lia|].
    rewrite Hloss. apply magic_selected_schedule__maximum_revenue; auto; lia. }
  assert (Ha0 : Forall (Z.le 0) a).
  { eapply Forall_impl; [|exact Ha]. intros z Hz. lia. }
  assert (Hlen : Zlength a = Zlength b).
  { rewrite !Zlength_correct, (Forall2_length Hab). reflexivity. }
  assert (Hupper : forall cash sc items,
    SetsClass.RelsDomain.clos_refl_trans (MagicTrade c a b)
      (0,(0,map (fun _ : Z => 0) a)) (cash,(sc,items)) ->
    Forall (eq 2) items -> cash <= UnconstrainedRevenue c a b-loss).
  { apply (magic_first_purchase_bound__maximum_revenue c a b
      (UnconstrainedRevenue c a b-loss)); [lia|lia|].
    intros cash0 items0 Hl Hstates Hraw Hcash0.
    pose proof (magic_raw_capital_accounting__maximum_revenue c a b cash0 items0
      Ha0 Hlen Hl Hstates Hraw) as Haccount.
    cbn zeta in Haccount. destruct Haccount as [Hfund Heq].
    assert (Hcandidate : loss <= Sum.sum
      (fun i => 0 <= i < Zlength a /\
        (Znth i items0 0 = 2 /\ 0 < Znth i b 0-Znth i a 0-c))
      (fun i => Znth i b 0-Znth i a 0-c)).
    { apply Hmin. right.
      exists (fun i => Znth i items0 0 = 2 /\ 0 < Znth i b 0-Znth i a 0-c).
      split; [intros i Hi HS; exact (proj2 HS)|]. split; [lia|reflexivity]. }
    lia. }
  unfold MaximumMagicRevenue, max_value_of_subset, max_object_of_subset.
  exists (UnconstrainedRevenue c a b-loss). split; [split|reflexivity].
  - exact Hatt.
  - intros cash [sc [items [Hrt Hall]]]. eapply Hupper; eauto.
Qed.
Lemma magic_default_bounds__prefix_totals : forall a b i,
  Forall (Z.le 1) a -> Forall2 Z.le a b ->
  Forall (Z.ge 10000) b ->
  0 <= Znth i a 0 /\ Znth i a 0 <= Znth i b 0 /\ Znth i b 0 <= 10000.
Proof.
  intros a b i Ha Hab Hb. unfold Znth.
  generalize (Z.to_nat i). clear i.
  induction Hab; intros n; inversion Ha; inversion Hb; subst;
    destruct n; simpl; try lia; auto.
Qed.
Lemma magic_pair_prefix_nat__prefix_totals : forall (f : Z * Z -> Z),
  f (0,0) = 0 -> forall n a b,
  length a = length b ->
  ListLib.sum (map f (combine (firstn (S n) a) (firstn (S n) b))) =
  ListLib.sum (map f (combine (firstn n a) (firstn n b))) +
  f (nth n a 0, nth n b 0).
Proof.
  intros f Hzero n. induction n; intros a b Hlen;
    destruct a; destruct b; simpl in *; try discriminate; try lia.
  specialize (IHn a b ltac:(lia)). lia.
Qed.
Lemma magic_sum_prefix_nat__prefix_totals : forall n a,
  ListLib.sum (firstn (S n) a) = ListLib.sum (firstn n a) + nth n a 0.
Proof.
  induction n; intros a; destruct a; simpl; rewrite ?firstn_nil, ?nth_nil; simpl; try lia.
  specialize (IHn a). simpl in IHn. lia.
Qed.
Lemma magic_prefix_step__prefix_totals : forall c a b i,
  0 <= c -> 0 <= i -> Forall2 Z.le a b ->
  ListLib.sum (sublist 0 (i+1) a) = ListLib.sum (sublist 0 i a) + Znth i a 0 /\
  UnconstrainedRevenue c (sublist 0 (i+1) a) (sublist 0 (i+1) b) =
    UnconstrainedRevenue c (sublist 0 i a) (sublist 0 i b) + Z.max (Znth i a 0) (Znth i b 0 - c) /\
  FreeCash c (sublist 0 (i+1) a) (sublist 0 (i+1) b) =
    FreeCash c (sublist 0 i a) (sublist 0 i b) +
      (if Z.leb (Znth i b 0 - Znth i a 0 - c) 0 then Znth i a 0 else 0).
Proof.
  intros c a b i Hc Hi Hab.
  pose proof (Forall2_length Hab) as Hlen.
  unfold UnconstrainedRevenue, FreeCash, sublist, Znth; simpl.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.
  split. { apply magic_sum_prefix_nat__prefix_totals. }
  split; apply magic_pair_prefix_nat__prefix_totals; auto; simpl.
  - rewrite Z.max_l by lia. reflexivity.
  - destruct (- c <=? 0); reflexivity.
Qed.
Lemma magic_empty_sum__dp_initialization (selected : Z -> Prop) (f : Z -> Z) :
  Sum.sum (fun i : Z => 0 <= i < 0 /\ selected i) f = 0.
Proof.
  transitivity (Sum.sum (fun i : Z => 0 <= i < 0 /\ selected i) (fun _ => 0)).
  - apply Sum.sum_ext. intros i [[? ?] ?]. lia.
  - apply Sum.sum_zero.
Qed.
Lemma magic_empty_minimum__dp_initialization c a b q :
  0 <= q -> MinimumSacrifice c a b 0 q (if Z.eq_dec q 0 then 0 else 10000001).
Proof.
  intros Hq. unfold MinimumSacrifice, min_value_of_subset, min_object_of_subset.
  destruct (Z.eq_dec q 0) as [Heq|Hne]; subst.
  - exists 0. split; [split|reflexivity].
    + right. exists (fun _ : Z => False). split; [intros; lia|].
      rewrite !magic_empty_sum__dp_initialization. auto.
    + intros value [Hv|[selected [Hp [Hcap Hv]]]].
      * subst. lia.
      * rewrite magic_empty_sum__dp_initialization in Hv. subst. lia.
  - exists 10000001. split; [split|reflexivity].
    + left. reflexivity.
    + intros value [Hv|[selected [Hp [Hcap Hv]]]].
      * subst. lia.
      * rewrite magic_empty_sum__dp_initialization in Hcap. lia.
Qed.
Lemma magic_init_tail__dp_initialization dl j :
  Zlength dl = j -> 1 <= j -> Znth 0 dl 0 = 0 ->
  Forall (eq 10000001) (sublist 1 j dl) ->
  exists tail, dl = 0 :: tail /\ Forall (eq 10000001) tail.
Proof.
  intros Hlen Hj Hhead Htail. destruct dl as [|x tail].
  - rewrite Zlength_nil in Hlen. lia.
  - change (x = 0) in Hhead. subst x. exists tail. split; [reflexivity|].
    rewrite sublist_cons2 in Htail by lia.
    replace (1-1) with 0 in Htail by lia.
    rewrite sublist_self in Htail; [exact Htail|].
    rewrite Zlength_cons in Hlen. lia.
Qed.
Lemma magic_Forall_nth__dp_initialization (P : Z -> Prop) l i :
  Forall P l -> 0 <= i < Zlength l -> P (Znth i l 0).
Proof.
  intros HF Hi. rewrite Forall_forall in HF. apply HF.
  unfold Znth. apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma item_bounds__prefix_safety : forall al bl i,
  Forall (Z.le 1) al -> Forall2 Z.le al bl ->
  Forall (Z.ge 10000) bl -> 0 <= i < Zlength al ->
  1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\
  Znth i bl 0 <= 10000.
Proof.
  intros al bl i Ha Hab Hb Hi.
  apply (Forall2_nth_iff Z Z Z.le al bl 0 0) in Hab.
  destruct Hab as [Hlen Hab].
  assert (Hia : (Z.to_nat i < length al)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  assert (Hib : (Z.to_nat i < length bl)%nat) by lia.
  rewrite Forall_forall in Ha, Hb.
  specialize (Ha _ (nth_In al 0 Hia)).
  specialize (Hb _ (nth_In bl 0 Hib)).
  specialize (Hab _ Hia).
  unfold Znth. lia.
Qed.
Lemma forall_Znth__dp_safety (P : Z -> Prop) l i :
  Forall P l -> 0 <= i < Zlength l -> P (Znth i l 0).
Proof.
  intros HF Hi. rewrite Forall_forall in HF.
  apply HF. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma forall2_Znth__dp_safety al bl i :
  Forall2 Z.le al bl -> 0 <= i < Zlength al ->
  Znth i al 0 <= Znth i bl 0.
Proof.
  intros HF Hi.
  apply (proj1 (Forall2_nth_iff Z Z Z.le al bl 0 0)) in HF.
  destruct HF as [_ HF]. apply HF.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma magic_forall_read__dp_projections (P : Z -> Prop) l d i :
  Forall P l -> P d -> P (Znth i l d).
Proof.
  intros H Hd. unfold Znth. generalize (Z.to_nat i).
  induction H; intros [|n]; simpl; auto.
Qed.
Lemma magic_forall_write__dp_projections (P : Z -> Prop) l v i :
  Forall P l -> P v -> Forall P (replace_Znth i v l).
Proof.
  intros H Hv. unfold replace_Znth. generalize (Z.to_nat i).
  induction H; intros [|n]; simpl; constructor; auto.
Qed.
Lemma magic_zero_minimum__dp_projections c a b upto loss :
  0 <= upto -> (MinimumSacrifice c a b upto 0 loss <-> loss = 0).
Proof.
  intros Hu.
  assert (Hz : forall f : Z -> Z,
    Sum.sum (fun i : Z => 0 <= i < upto /\ False) f = 0).
  { intros f. rewrite (Sum.sum_ext _ f (fun _ => 0));
      [apply Sum.sum_zero | intros x [_ H]; contradiction]. }
  assert (Hcandidate : 0 = 10000001 \/
    exists selected : Z -> Prop,
      (forall i, 0 <= i < upto -> selected i ->
        0 < Znth i b 0 - Znth i a 0 - c) /\
      0 <= Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
        (fun i => Znth i a 0) /\
      0 = Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
        (fun i => Znth i b 0 - Znth i a 0 - c)).
  { right. exists (fun _ => False). split; [tauto|]. rewrite !Hz. lia. }
  assert (Hnonneg : forall value,
    (value = 10000001 \/
      exists selected : Z -> Prop,
        (forall i, 0 <= i < upto -> selected i ->
          0 < Znth i b 0 - Znth i a 0 - c) /\
        0 <= Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
          (fun i => Znth i a 0) /\
        value = Sum.sum (fun i : Z => 0 <= i < upto /\ selected i)
          (fun i => Znth i b 0 - Znth i a 0 - c)) -> 0 <= value).
  { intros value [-> | [selected [Hp [_ ->]]]]; [lia|].
    apply Sum.sum_nonneg. intros x [Hx Hsel]. specialize (Hp x Hx Hsel). lia. }
  unfold MinimumSacrifice, min_value_of_subset, min_object_of_subset.
  split.
  - intros [v [[Hv Hmin] ->]]. specialize (Hmin 0 Hcandidate).
    pose proof (Hnonneg _ Hv). lia.
  - intros ->. exists 0. repeat split; auto.
Qed.
