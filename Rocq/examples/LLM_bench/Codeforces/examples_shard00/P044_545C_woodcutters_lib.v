Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition TreeOccupation (tree : Z*Z) (choice left right : Z) : Prop :=
  (choice = -1 /\ left = fst tree - snd tree /\ right = fst tree) \/
  (choice = 0 /\ left = fst tree /\ right = fst tree) \/
  (choice = 1 /\ left = fst tree /\ right = fst tree + snd tree).
Definition ValidFelling (trees : list (Z*Z)) (choices : list Z) : Prop :=
  Zlength choices = Zlength trees /\ Forall (fun d => d = -1 \/ d = 0 \/ d = 1) choices /\
  forall i, 0 <= i < Zlength trees - 1 -> exists li ri lj rj,
    TreeOccupation (Znth i trees (0,0)) (Znth i choices 0) li ri /\
    TreeOccupation (Znth (i+1) trees (0,0)) (Znth (i+1) choices 0) lj rj /\ ri < lj.
Definition Pre (trees : list (Z*Z)) : Prop := 1 <= Zlength trees <= 100000 /\
  Forall (fun p => 1 <= fst p <= 1000000000 /\ 1 <= snd p <= 1000000000) trees /\
  mono_inc (map fst trees).
Definition Spec (trees : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le (ValidFelling trees)
    (fun choices => Zlength (filter (fun x => negb (Z.eqb x 0)) choices)) out.

(** The number of felled trees represented by a list of choices. *)
Definition FellingCount (choices : list Z) : Z :=
  Zlength (filter (fun choice => negb (Z.eqb choice 0)) choices).

(** A prefix choice is admissible when it is internally non-overlapping and
    leaves enough room for the next, still unprocessed tree to stand.  The
    endpoint is the right edge occupied by the last tree in the prefix. *)
Definition PrefixFellingAdmissible
    (trees : list (Z * Z)) (processed : Z)
    (choices : list Z) (endpoint : Z) : Prop :=
  1 <= processed < Zlength trees /\
  ValidFelling (sublist 0 processed trees) choices /\
  (exists left,
    TreeOccupation (Znth (processed - 1) trees (0, 0))
      (Znth (processed - 1) choices 0) left endpoint) /\
  endpoint < fst (Znth processed trees (0, 0)).

(** Mathematical state of the left-to-right greedy scan.  [answer] includes
    the final tree, which is reserved throughout the scan.  The selected
    prefix maximizes the number of felled trees among admissible prefixes;
    among equally good prefixes its occupied endpoint is minimal. *)
Definition PrefixFellingState
    (trees : list (Z * Z))
    (processed occupied answer : Z) : Prop :=
  exists choices,
    PrefixFellingAdmissible trees processed choices occupied /\
    answer = 1 + FellingCount choices /\
    forall competitor competitor_endpoint,
      PrefixFellingAdmissible
        trees processed competitor competitor_endpoint ->
      FellingCount competitor <= FellingCount choices /\
      (FellingCount competitor = FellingCount choices ->
       occupied <= competitor_endpoint).

Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Psatz.
Lemma Znth_app_left__prefix_transitions :
  forall {A : Type} (d : A) (l1 l2 : list A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_last__prefix_transitions :
  forall {A : Type} (d x : A) (l : list A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A d x l.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength l) - length l)%nat with 0%nat.
    + reflexivity.
    + rewrite Zlength_correct, Nat2Z.id. lia.
  - rewrite Zlength_correct, Nat2Z.id. lia.
Qed.
Lemma sublist_snoc__prefix_transitions :
  forall {A : Type} (d : A) (l : list A) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.
Lemma FellingCount_snoc_felled__prefix_transitions :
  forall choices d,
    d <> 0 ->
    FellingCount (choices ++ d :: nil) = FellingCount choices + 1.
Proof.
  intros choices d Hd.
  unfold FellingCount.
  rewrite filter_app, !Zlength_app.
  simpl.
  destruct (Z.eqb d 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - simpl. rewrite Zlength_cons, Zlength_nil. lia.
Qed.
Lemma FellingCount_snoc_stand__prefix_transitions :
  forall choices,
    FellingCount (choices ++ 0 :: nil) = FellingCount choices.
Proof.
  intros choices.
  unfold FellingCount.
  rewrite filter_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma FellingCount_snoc_bound__prefix_transitions :
  forall choices d,
    FellingCount (choices ++ d :: nil) <= FellingCount choices + 1.
Proof.
  intros choices d.
  unfold FellingCount.
  rewrite filter_app, Zlength_app.
  simpl.
  destruct (Z.eqb d 0); simpl; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.
Lemma Zlength_filter_le__prefix_transitions :
  forall {A : Type} (f : A -> bool) xs,
    Zlength (filter f xs) <= Zlength xs.
Proof.
  intros A f xs.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. destruct (f x); rewrite ?Zlength_cons; lia.
Qed.
Lemma FellingCount_le_length__prefix_transitions :
  forall choices, FellingCount choices <= Zlength choices.
Proof.
  intros choices.
  unfold FellingCount.
  apply Zlength_filter_le__prefix_transitions.
Qed.
Lemma Znth_map__prefix_transitions :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_map__prefix_transitions :
  forall {A B : Type} (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs.
  rewrite !Zlength_correct, length_map.
  reflexivity.
Qed.
Lemma choices_snoc_decompose__prefix_transitions :
  forall choices i,
    0 <= i ->
    Zlength choices = i + 1 ->
    choices = sublist 0 i choices ++ Znth i choices 0 :: nil.
Proof.
  intros choices i Hi Hlen.
  rewrite <- (sublist_self choices (i + 1)) at 1 by lia.
  apply sublist_snoc__prefix_transitions.
  lia.
Qed.
Lemma TreeOccupation_choice__prefix_transitions :
  forall tree choice left right,
    TreeOccupation tree choice left right ->
    choice = -1 \/ choice = 0 \/ choice = 1.
Proof.
  intros tree choice left right H.
  unfold TreeOccupation in H.
  tauto.
Qed.
Lemma TreeOccupation_left_le__prefix_transitions :
  forall tree choice left right,
    0 <= snd tree ->
    TreeOccupation tree choice left right ->
    left <= fst tree.
Proof.
  intros tree choice left right Hheight H.
  unfold TreeOccupation in H.
  destruct H as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]; subst; lia.
Qed.
Lemma TreeOccupation_felled_endpoint__prefix_transitions :
  forall tree choice left right,
    0 <= snd tree ->
    choice <> 0 ->
    TreeOccupation tree choice left right ->
    fst tree <= right.
Proof.
  intros tree choice left right Hheight Hchoice H.
  unfold TreeOccupation in H.
  destruct H as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]; subst; try contradiction; lia.
Qed.
Lemma TreeOccupation_unique__prefix_transitions :
  forall tree choice left1 right1 left2 right2,
    TreeOccupation tree choice left1 right1 ->
    TreeOccupation tree choice left2 right2 ->
    left1 = left2 /\ right1 = right2.
Proof.
  intros tree choice left1 right1 left2 right2 H1 H2.
  unfold TreeOccupation in *.
  destruct H1 as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]];
  destruct H2 as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]];
  subst; try lia; split; reflexivity.
Qed.
Lemma Pre_height_pos__prefix_transitions :
  forall trees i,
    Pre trees ->
    0 <= i < Zlength trees ->
    1 <= snd (Znth i trees (0, 0)).
Proof.
  intros trees i Hpre Hi.
  unfold Pre in Hpre.
  destruct Hpre as [_ [Hall _]].
  pose proof (proj1 (Forall_Znth
    (fun p : Z * Z => 1 <= fst p <= 1000000000 /\
                         1 <= snd p <= 1000000000)
    (0, 0) trees) Hall i Hi) as Hbounds.
  destruct Hbounds as [_ [Hsnd _]].
  exact Hsnd.
Qed.
Lemma Pre_position_inc__prefix_transitions :
  forall trees i j,
    Pre trees ->
    0 <= i -> i < j -> j < Zlength trees ->
    fst (Znth i trees (0, 0)) < fst (Znth j trees (0, 0)).
Proof.
  intros trees i j Hpre Hi Hij Hj.
  unfold Pre in Hpre.
  destruct Hpre as [_ [_ Hmono]].
  specialize (Hmono i j Hi Hij).
  rewrite Zlength_map__prefix_transitions in Hmono.
  specialize (Hmono Hj).
  rewrite (Znth_map__prefix_transitions fst trees (0, 0) 0 i) in Hmono by lia.
  rewrite (Znth_map__prefix_transitions fst trees (0, 0) 0 j) in Hmono by lia.
  exact Hmono.
Qed.
Lemma ValidFelling_extend__prefix_transitions :
  forall trees i choices old_left old_endpoint choice new_left new_endpoint,
    1 <= i ->
    i < Zlength trees ->
    ValidFelling (sublist 0 i trees) choices ->
    TreeOccupation (Znth (i - 1) trees (0, 0))
      (Znth (i - 1) choices 0) old_left old_endpoint ->
    TreeOccupation (Znth i trees (0, 0)) choice new_left new_endpoint ->
    old_endpoint < new_left ->
    ValidFelling (sublist 0 (i + 1) trees) (choices ++ choice :: nil).
Proof.
  intros trees i choices old_left old_endpoint choice new_left new_endpoint
    Hi Hilen Hvalid Hold Hnew Hsep.
  unfold ValidFelling in *.
  destruct Hvalid as [Hlen [Hall Hpairs]].
  assert (Hsub_i : Zlength (sublist 0 i trees) = i).
  { apply Zlength_sublist0. lia. }
  assert (Hsub_s : Zlength (sublist 0 (i + 1) trees) = i + 1).
  { apply Zlength_sublist0. lia. }
  rewrite Hsub_i in Hlen.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hsub_s. lia.
  - split.
    + apply Forall_app. split; [exact Hall |].
      constructor.
      * eapply TreeOccupation_choice__prefix_transitions; eauto.
      * constructor.
    + intros j Hj.
      rewrite Hsub_s in Hj.
      rewrite !Znth_sublist0 by lia.
      destruct (Z.eq_dec j (i - 1)) as [-> | Hjne].
      * exists old_left, old_endpoint, new_left, new_endpoint.
        rewrite Znth_app_left__prefix_transitions by lia.
        replace (Znth (i - 1 + 1) (choices ++ choice :: nil) 0) with choice.
        2: { replace (i - 1 + 1) with (Zlength choices) by lia.
             symmetry. apply Znth_app_last__prefix_transitions. }
        replace (i - 1 + 1) with i by lia.
        repeat split; assumption.
      * assert (Hjold : 0 <= j < Zlength (sublist 0 i trees) - 1) by
            (rewrite Hsub_i; lia).
        specialize (Hpairs j Hjold).
        rewrite !Znth_sublist0 in Hpairs by lia.
        rewrite !Znth_app_left__prefix_transitions by lia.
        exact Hpairs.
Qed.
Lemma ValidFelling_prefix__prefix_transitions :
  forall trees i prefix choice,
    1 <= i ->
    i < Zlength trees ->
    ValidFelling (sublist 0 (i + 1) trees) (prefix ++ choice :: nil) ->
    ValidFelling (sublist 0 i trees) prefix.
Proof.
  intros trees i prefix choice Hi Hilen Hvalid.
  unfold ValidFelling in *.
  destruct Hvalid as [Hlen [Hall Hpairs]].
  assert (Hsub_i : Zlength (sublist 0 i trees) = i).
  { apply Zlength_sublist0. lia. }
  assert (Hsub_s : Zlength (sublist 0 (i + 1) trees) = i + 1).
  { apply Zlength_sublist0. lia. }
  rewrite Zlength_app, Zlength_cons, Zlength_nil, Hsub_s in Hlen.
  split.
  - rewrite Hsub_i. lia.
  - split.
    + apply Forall_app in Hall. tauto.
    + intros j Hj.
      rewrite Hsub_i in Hj.
      assert (Hjbig : 0 <= j < Zlength (sublist 0 (i + 1) trees) - 1) by
          (rewrite Hsub_s; lia).
      specialize (Hpairs j Hjbig).
      rewrite !Znth_sublist0 in Hpairs by lia.
      rewrite !Znth_sublist0 by lia.
      rewrite !Znth_app_left__prefix_transitions in Hpairs by lia.
      exact Hpairs.
Qed.
Lemma ValidFelling_boundary__prefix_transitions :
  forall trees i prefix choice,
    1 <= i ->
    i < Zlength trees ->
    ValidFelling (sublist 0 (i + 1) trees) (prefix ++ choice :: nil) ->
    exists old_left old_endpoint new_left new_endpoint,
      TreeOccupation (Znth (i - 1) trees (0, 0))
        (Znth (i - 1) prefix 0) old_left old_endpoint /\
      TreeOccupation (Znth i trees (0, 0)) choice new_left new_endpoint /\
      old_endpoint < new_left.
Proof.
  intros trees i prefix choice Hi Hilen Hvalid.
  unfold ValidFelling in Hvalid.
  destruct Hvalid as [Hlen [_ Hpairs]].
  assert (Hsub_s : Zlength (sublist 0 (i + 1) trees) = i + 1).
  { apply Zlength_sublist0. lia. }
  rewrite Zlength_app, Zlength_cons, Zlength_nil, Hsub_s in Hlen.
  specialize (Hpairs (i - 1)).
  assert (Hb : 0 <= i - 1 < Zlength (sublist 0 (i + 1) trees) - 1) by
      (rewrite Hsub_s; lia).
  specialize (Hpairs Hb).
  rewrite !Znth_sublist0 in Hpairs by lia.
  rewrite Znth_app_left__prefix_transitions in Hpairs by lia.
  replace (Znth (i - 1 + 1) (prefix ++ choice :: nil) 0) with choice in Hpairs.
  2: { replace (i - 1 + 1) with (Zlength prefix) by lia.
       symmetry. apply Znth_app_last__prefix_transitions. }
  replace (i - 1 + 1) with i in Hpairs by lia.
  exact Hpairs.
Qed.
Lemma PrefixFellingAdmissible_decompose__prefix_transitions :
  forall trees i competitor competitor_endpoint,
    Pre trees ->
    1 <= i ->
    PrefixFellingAdmissible trees (i + 1) competitor competitor_endpoint ->
    exists prefix choice old_endpoint new_left,
      competitor = prefix ++ choice :: nil /\
      PrefixFellingAdmissible trees i prefix old_endpoint /\
      TreeOccupation (Znth i trees (0, 0)) choice
        new_left competitor_endpoint /\
      old_endpoint < new_left.
Proof.
  intros trees i competitor competitor_endpoint Hpre Hi Hadm.
  unfold PrefixFellingAdmissible in Hadm.
  destruct Hadm as [Hrange [Hvalid [[last_left Hlast] Hnext]]].
  assert (Hsub_s : Zlength (sublist 0 (i + 1) trees) = i + 1).
  { apply Zlength_sublist0. lia. }
  unfold ValidFelling in Hvalid at 1.
  destruct Hvalid as [Hcomplen Hvalid_rest].
  rewrite Hsub_s in Hcomplen.
  assert (Hvalid : ValidFelling (sublist 0 (i + 1) trees) competitor).
  { unfold ValidFelling. split.
    - rewrite Hsub_s. exact Hcomplen.
    - exact Hvalid_rest. }
  pose proof (choices_snoc_decompose__prefix_transitions competitor i
    ltac:(lia) Hcomplen) as Hdecomp.
  remember (sublist 0 i competitor) as prefix.
  remember (Znth i competitor 0) as choice.
  rewrite Hdecomp in Hvalid.
  pose proof (ValidFelling_prefix__prefix_transitions
    trees i prefix choice Hi ltac:(lia) Hvalid) as Hprefix_valid.
  pose proof (ValidFelling_boundary__prefix_transitions
    trees i prefix choice Hi ltac:(lia) Hvalid) as Hboundary.
  destruct Hboundary as
    [old_left [old_endpoint [new_left [new_endpoint
      [Hold [Hnew Hsep]]]]]].
  rewrite Hdecomp in Hlast.
  replace (i + 1 - 1) with i in Hlast by lia.
  assert (Hprefix_len : Zlength prefix = i).
  { unfold ValidFelling in Hprefix_valid.
    destruct Hprefix_valid as [Hprefix_len _].
    rewrite Zlength_sublist0 in Hprefix_len by lia.
    exact Hprefix_len. }
  assert (Hchoice_at : Znth i (prefix ++ choice :: nil) 0 = choice).
  { replace i with (Zlength prefix) by lia.
    apply Znth_app_last__prefix_transitions. }
  rewrite Hchoice_at in Hlast.
  pose proof (TreeOccupation_unique__prefix_transitions
    (Znth i trees (0, 0)) choice new_left new_endpoint
    last_left competitor_endpoint Hnew Hlast) as Hunique.
  destruct Hunique as [Hleft Hend]. subst last_left new_endpoint.
  assert (Hheight : 0 <= snd (Znth i trees (0, 0))).
  { pose proof (Pre_height_pos__prefix_transitions trees i Hpre ltac:(lia)). lia. }
  exists prefix, choice, old_endpoint, new_left.
  split.
  - exact Hdecomp.
  - split.
    + unfold PrefixFellingAdmissible.
      split; [lia |].
      split; [exact Hprefix_valid |].
      split.
      * exists old_left. exact Hold.
      * eapply Z.lt_le_trans; [exact Hsep |].
        eapply TreeOccupation_left_le__prefix_transitions; eauto.
    + tauto.
Qed.
Lemma FellingCount_one_nonzero__prefix_transitions :
  forall choices,
    Zlength choices = 1 ->
    FellingCount choices = 1 ->
    Znth 0 choices 0 <> 0.
Proof.
  intros choices Hlen Hcount Hzero.
  pose proof (choices_snoc_decompose__prefix_transitions choices 0
    ltac:(lia) ltac:(lia)) as Hdecomp.
  assert (sublist 0 0 choices = nil).
  { reflexivity. }
  rewrite H, Hzero in Hdecomp.
  subst choices.
  unfold FellingCount in Hcount.
  simpl in Hcount.
  rewrite Zlength_nil in Hcount.
  lia.
Qed.
Lemma PrefixFellingState_init__prefix_transitions :
  forall trees,
    Pre trees ->
    3 <= Zlength trees ->
    PrefixFellingState trees 1 (fst (Znth 0 trees (0, 0))) 2.
Proof.
  intros trees Hpre Hlen.
  unfold PrefixFellingState.
  exists (-1 :: nil).
  split.
  - unfold PrefixFellingAdmissible.
    split; [lia |].
    split.
    + unfold ValidFelling.
      assert (Hsub : Zlength (sublist 0 1 trees) = 1).
      { apply Zlength_sublist0. lia. }
      split.
      * rewrite Zlength_cons, Zlength_nil, Hsub. lia.
      * split.
        -- repeat constructor; lia.
        -- intros j Hj. rewrite Hsub in Hj. lia.
    + split.
      * exists (fst (Znth 0 trees (0, 0)) - snd (Znth 0 trees (0, 0))).
        replace (1 - 1) with 0 by lia.
        simpl. unfold TreeOccupation. left. repeat split; reflexivity.
      * eapply Pre_position_inc__prefix_transitions; eauto; lia.
  - split.
    + unfold FellingCount. simpl. reflexivity.
    + intros competitor competitor_endpoint Hcompetitor.
      assert (Hcompetitor_len : Zlength competitor = 1).
      { unfold PrefixFellingAdmissible in Hcompetitor.
        destruct Hcompetitor as [_ [Hvalid _]].
        unfold ValidFelling in Hvalid.
        destruct Hvalid as [Hvalid_len _].
        rewrite Zlength_sublist0 in Hvalid_len by lia.
        exact Hvalid_len. }
      split.
      * assert (FellingCount (-1 :: nil) = 1) by reflexivity.
        rewrite H.
        rewrite <- Hcompetitor_len.
        apply FellingCount_le_length__prefix_transitions.
      * intros Hcount.
        unfold FellingCount in Hcount at 2.
        simpl in Hcount.
        assert (Hnonzero : Znth 0 competitor 0 <> 0).
        { apply FellingCount_one_nonzero__prefix_transitions; assumption. }
        unfold PrefixFellingAdmissible in Hcompetitor.
        destruct Hcompetitor as [_ [_ [[left Hoccupation] _]]].
        replace (1 - 1) with 0 in Hoccupation by lia.
        pose proof (Pre_height_pos__prefix_transitions trees 0 Hpre ltac:(lia))
          as Hheight.
        eapply TreeOccupation_felled_endpoint__prefix_transitions; eauto; lia.
Qed.
Lemma PrefixFellingState_step_left__prefix_transitions :
  forall trees i occupied answer,
    Pre trees ->
    1 <= i ->
    i + 1 < Zlength trees ->
    PrefixFellingState trees i occupied answer ->
    fst (Znth i trees (0, 0)) - snd (Znth i trees (0, 0)) > occupied ->
    PrefixFellingState trees (i + 1) (fst (Znth i trees (0, 0)))
      (answer + 1).
Proof.
  intros trees i occupied answer Hpre Hi Hnext Hstate Hleft.
  unfold PrefixFellingState in Hstate.
  destruct Hstate as [choices [Hadm [Hanswer Hoptimal]]].
  unfold PrefixFellingAdmissible in Hadm.
  destruct Hadm as [Hrange [Hvalid [[old_left Hold] Hold_next]]].
  assert (Hchoices_len : Zlength choices = i).
  { unfold ValidFelling in Hvalid.
    destruct Hvalid as [Hvalid_len _].
    rewrite Zlength_sublist0 in Hvalid_len by lia.
    exact Hvalid_len. }
  unfold PrefixFellingState.
  exists (choices ++ -1 :: nil).
  split.
  - unfold PrefixFellingAdmissible.
    split; [lia |].
    split.
    + eapply ValidFelling_extend__prefix_transitions with
        (old_left := old_left)
        (old_endpoint := occupied)
        (new_left := fst (Znth i trees (0, 0)) - snd (Znth i trees (0, 0)))
        (new_endpoint := fst (Znth i trees (0, 0))).
      * exact Hi.
      * lia.
      * exact Hvalid.
      * exact Hold.
      * unfold TreeOccupation. left. repeat split; reflexivity.
      * lia.
    + split.
      * exists (fst (Znth i trees (0, 0)) - snd (Znth i trees (0, 0))).
        replace (i + 1 - 1) with i by lia.
        replace (Znth i (choices ++ -1 :: nil) 0) with (-1).
        2: { replace i with (Zlength choices) by lia.
             symmetry. apply Znth_app_last__prefix_transitions. }
        unfold TreeOccupation. left. repeat split; reflexivity.
      * eapply Pre_position_inc__prefix_transitions; eauto; lia.
  - split.
    + rewrite FellingCount_snoc_felled__prefix_transitions by lia.
      lia.
    + intros competitor competitor_endpoint Hcompetitor.
      pose proof (PrefixFellingAdmissible_decompose__prefix_transitions
        trees i competitor competitor_endpoint Hpre Hi Hcompetitor) as Hdec.
      destruct Hdec as [prefix [choice [prefix_endpoint [new_left
        [Hcomp [Hprefix [Hoccupation Hsep]]]]]]].
      pose proof (Hoptimal prefix prefix_endpoint Hprefix) as Hprefix_opt.
      destruct Hprefix_opt as [Hcount_le Hendpoint_min].
      assert (Hselected_count :
        FellingCount (choices ++ -1 :: nil) = FellingCount choices + 1).
      { apply FellingCount_snoc_felled__prefix_transitions. lia. }
      rewrite Hcomp.
      split.
      * pose proof (FellingCount_snoc_bound__prefix_transitions prefix choice).
        rewrite Hselected_count.
        lia.
      * intros Hcount_eq.
        rewrite Hselected_count in Hcount_eq.
        assert (Hchoice_nonzero : choice <> 0).
        { intro Hzero. subst choice.
          rewrite FellingCount_snoc_stand__prefix_transitions in Hcount_eq.
          lia. }
        pose proof (Pre_height_pos__prefix_transitions trees i Hpre ltac:(lia))
          as Hheight.
        eapply TreeOccupation_felled_endpoint__prefix_transitions; eauto; lia.
Qed.
Lemma PrefixFellingState_step_right__prefix_transitions :
  forall trees i occupied answer,
    Pre trees ->
    1 <= i ->
    i + 1 < Zlength trees ->
    PrefixFellingState trees i occupied answer ->
    fst (Znth i trees (0, 0)) - snd (Znth i trees (0, 0)) <= occupied ->
    fst (Znth i trees (0, 0)) + snd (Znth i trees (0, 0)) <
      fst (Znth (i + 1) trees (0, 0)) ->
    PrefixFellingState trees (i + 1)
      (fst (Znth i trees (0, 0)) + snd (Znth i trees (0, 0)))
      (answer + 1).
Proof.
  intros trees i occupied answer Hpre Hi Hnext Hstate Hleft_failed Hright.
  unfold PrefixFellingState in Hstate.
  destruct Hstate as [choices [Hadm [Hanswer Hoptimal]]].
  unfold PrefixFellingAdmissible in Hadm.
  destruct Hadm as [Hrange [Hvalid [[old_left Hold] Hold_next]]].
  assert (Hchoices_len : Zlength choices = i).
  { unfold ValidFelling in Hvalid.
    destruct Hvalid as [Hvalid_len _].
    rewrite Zlength_sublist0 in Hvalid_len by lia.
    exact Hvalid_len. }
  unfold PrefixFellingState.
  exists (choices ++ 1 :: nil).
  split.
  - unfold PrefixFellingAdmissible.
    split; [lia |].
    split.
    + eapply ValidFelling_extend__prefix_transitions with
        (old_left := old_left)
        (old_endpoint := occupied)
        (new_left := fst (Znth i trees (0, 0)))
        (new_endpoint := fst (Znth i trees (0, 0)) + snd (Znth i trees (0, 0))).
      * exact Hi.
      * lia.
      * exact Hvalid.
      * exact Hold.
      * unfold TreeOccupation. right. right. repeat split; reflexivity.
      * exact Hold_next.
    + split.
      * exists (fst (Znth i trees (0, 0))).
        replace (i + 1 - 1) with i by lia.
        replace (Znth i (choices ++ 1 :: nil) 0) with 1.
        2: { replace i with (Zlength choices) by lia.
             symmetry. apply Znth_app_last__prefix_transitions. }
        unfold TreeOccupation. right. right. repeat split; reflexivity.
      * exact Hright.
  - split.
    + rewrite FellingCount_snoc_felled__prefix_transitions by lia.
      lia.
    + intros competitor competitor_endpoint Hcompetitor.
      pose proof (PrefixFellingAdmissible_decompose__prefix_transitions
        trees i competitor competitor_endpoint Hpre Hi Hcompetitor) as Hdec.
      destruct Hdec as [prefix [choice [prefix_endpoint [new_left
        [Hcomp [Hprefix [Hoccupation Hsep]]]]]]].
      pose proof (Hoptimal prefix prefix_endpoint Hprefix) as Hprefix_opt.
      destruct Hprefix_opt as [Hcount_le Hendpoint_min].
      assert (Hselected_count :
        FellingCount (choices ++ 1 :: nil) = FellingCount choices + 1).
      { apply FellingCount_snoc_felled__prefix_transitions. lia. }
      rewrite Hcomp.
      split.
      * pose proof (FellingCount_snoc_bound__prefix_transitions prefix choice).
        rewrite Hselected_count. lia.
      * intros Hcount_eq.
        rewrite Hselected_count in Hcount_eq.
        unfold TreeOccupation in Hoccupation.
        destruct Hoccupation as
          [[Hchoice [Hnew_left Hend]] |
           [[Hchoice [Hnew_left Hend]] | [Hchoice [Hnew_left Hend]]]].
        -- subst choice new_left competitor_endpoint.
           rewrite FellingCount_snoc_felled__prefix_transitions in Hcount_eq by lia.
           assert (FellingCount prefix = FellingCount choices) by lia.
           specialize (Hendpoint_min H).
           lia.
        -- subst choice new_left competitor_endpoint.
           rewrite FellingCount_snoc_stand__prefix_transitions in Hcount_eq.
           lia.
        -- subst choice new_left competitor_endpoint. lia.
Qed.
Lemma PrefixFellingState_step_stand__prefix_transitions :
  forall trees i occupied answer,
    Pre trees ->
    1 <= i ->
    i + 1 < Zlength trees ->
    PrefixFellingState trees i occupied answer ->
    fst (Znth i trees (0, 0)) - snd (Znth i trees (0, 0)) <= occupied ->
    fst (Znth i trees (0, 0)) + snd (Znth i trees (0, 0)) >=
      fst (Znth (i + 1) trees (0, 0)) ->
    PrefixFellingState trees (i + 1) (fst (Znth i trees (0, 0))) answer.
Proof.
  intros trees i occupied answer Hpre Hi Hnext Hstate Hleft_failed Hright_failed.
  unfold PrefixFellingState in Hstate.
  destruct Hstate as [choices [Hadm [Hanswer Hoptimal]]].
  unfold PrefixFellingAdmissible in Hadm.
  destruct Hadm as [Hrange [Hvalid [[old_left Hold] Hold_next]]].
  assert (Hchoices_len : Zlength choices = i).
  { unfold ValidFelling in Hvalid.
    destruct Hvalid as [Hvalid_len _].
    rewrite Zlength_sublist0 in Hvalid_len by lia.
    exact Hvalid_len. }
  unfold PrefixFellingState.
  exists (choices ++ 0 :: nil).
  split.
  - unfold PrefixFellingAdmissible.
    split; [lia |].
    split.
    + eapply ValidFelling_extend__prefix_transitions with
        (old_left := old_left)
        (old_endpoint := occupied)
        (new_left := fst (Znth i trees (0, 0)))
        (new_endpoint := fst (Znth i trees (0, 0))).
      * exact Hi.
      * lia.
      * exact Hvalid.
      * exact Hold.
      * unfold TreeOccupation. right. left. repeat split; reflexivity.
      * exact Hold_next.
    + split.
      * exists (fst (Znth i trees (0, 0))).
        replace (i + 1 - 1) with i by lia.
        replace (Znth i (choices ++ 0 :: nil) 0) with 0.
        2: { replace i with (Zlength choices) by lia.
             symmetry. apply Znth_app_last__prefix_transitions. }
        unfold TreeOccupation. right. left. repeat split; reflexivity.
      * eapply Pre_position_inc__prefix_transitions; eauto; lia.
  - split.
    + rewrite FellingCount_snoc_stand__prefix_transitions. exact Hanswer.
    + intros competitor competitor_endpoint Hcompetitor.
      pose proof (PrefixFellingAdmissible_decompose__prefix_transitions
        trees i competitor competitor_endpoint Hpre Hi Hcompetitor) as Hdec.
      destruct Hdec as [prefix [choice [prefix_endpoint [new_left
        [Hcomp [Hprefix [Hoccupation Hsep]]]]]]].
      pose proof (Hoptimal prefix prefix_endpoint Hprefix) as Hprefix_opt.
      destruct Hprefix_opt as [Hcount_le Hendpoint_min].
      assert (Hselected_count :
        FellingCount (choices ++ 0 :: nil) = FellingCount choices).
      { apply FellingCount_snoc_stand__prefix_transitions. }
      assert (Hcompetitor_next :
        competitor_endpoint < fst (Znth (i + 1) trees (0, 0))).
      { unfold PrefixFellingAdmissible in Hcompetitor.
        destruct Hcompetitor as [_ [_ [_ Hcompetitor_next]]].
        exact Hcompetitor_next. }
      rewrite Hcomp.
      split.
      * rewrite Hselected_count.
        unfold TreeOccupation in Hoccupation.
        destruct Hoccupation as
          [[Hchoice [Hnew_left Hend]] |
           [[Hchoice [Hnew_left Hend]] | [Hchoice [Hnew_left Hend]]]].
        -- subst choice new_left competitor_endpoint.
           rewrite FellingCount_snoc_felled__prefix_transitions by lia.
           destruct (Z.eq_dec (FellingCount prefix) (FellingCount choices))
             as [Heq | Hneq].
           ++ specialize (Hendpoint_min Heq). lia.
           ++ lia.
        -- subst choice new_left competitor_endpoint.
           rewrite FellingCount_snoc_stand__prefix_transitions. lia.
        -- subst choice new_left competitor_endpoint. lia.
      * intros Hcount_eq.
        unfold TreeOccupation in Hoccupation.
        destruct Hoccupation as
          [[Hchoice [Hnew_left Hend]] |
           [[Hchoice [Hnew_left Hend]] | [Hchoice [Hnew_left Hend]]]].
        -- subst choice new_left competitor_endpoint. lia.
        -- subst choice new_left competitor_endpoint. lia.
        -- subst choice new_left competitor_endpoint. lia.
Qed.
Lemma TreeOccupation_left_le_fst__final_general :
  forall tree choice left right,
    1 <= snd tree ->
    TreeOccupation tree choice left right ->
    left <= fst tree.
Proof.
  intros tree choice left right Hheight Hocc.
  unfold TreeOccupation in Hocc.
  destruct Hocc as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]];
    subst; lia.
Qed.
Lemma ValidFelling_prefix__final_general :
  forall trees choices processed,
    0 <= processed <= Zlength trees ->
    ValidFelling trees choices ->
    ValidFelling (sublist 0 processed trees) (sublist 0 processed choices).
Proof.
  intros trees choices processed Hprocessed Hvalid.
  destruct Hvalid as [Hlength [Hall Hadj]].
  unfold ValidFelling.
  assert (Htrees : Zlength (sublist 0 processed trees) = processed).
  { apply Zlength_sublist0. lia. }
  assert (Hchoices : Zlength (sublist 0 processed choices) = processed).
  { apply Zlength_sublist0. lia. }
  split.
  - lia.
  - split.
    + apply (proj2 (Forall_Znth (fun d => d = -1 \/ d = 0 \/ d = 1) 0 _)).
      intros j Hj.
      rewrite Hchoices in Hj.
      rewrite Znth_sublist by lia.
      apply (proj1 (Forall_Znth (fun d => d = -1 \/ d = 0 \/ d = 1) 0 choices));
        auto; lia.
    + intros j Hj.
      rewrite Htrees in Hj.
      specialize (Hadj j ltac:(lia)).
      destruct Hadj as (li & ri & lj & rj & Hoi & Hoj & Hsep).
      exists li, ri, lj, rj.
      rewrite !Znth_sublist by lia.
      replace (j + 0) with j by lia.
      replace (j + 1 + 0) with (j + 1) by lia.
      exact (conj Hoi (conj Hoj Hsep)).
Qed.
Lemma ValidFelling_append_right__final_general :
  forall trees processed choices endpoint,
    1 <= processed ->
    processed + 1 = Zlength trees ->
    ValidFelling (sublist 0 processed trees) choices ->
    (exists left,
      TreeOccupation (Znth (processed - 1) trees (0, 0))
        (Znth (processed - 1) choices 0) left endpoint) ->
    endpoint < fst (Znth processed trees (0, 0)) ->
    ValidFelling trees (choices ++ 1 :: nil).
Proof.
  intros trees processed choices endpoint Hprocessed Htree_length
    Hvalid Hoccupation Hendpoint.
  destruct Hvalid as [Hchoice_length [Hall Hadj]].
  assert (Hprefix_length : Zlength (sublist 0 processed trees) = processed).
  { apply Zlength_sublist0. lia. }
  assert (Hchoices : Zlength choices = processed) by lia.
  unfold ValidFelling.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + apply Forall_app. split; [exact Hall | repeat constructor; lia].
    + intros j Hj.
      destruct (Z_lt_ge_dec j (processed - 1)) as [Hbefore | Hlast].
      * specialize (Hadj j ltac:(rewrite Hprefix_length; lia)).
        destruct Hadj as (li & ri & lj & rj & Hoi & Hoj & Hsep).
        exists li, ri, lj, rj.
        rewrite !app_Znth1 by lia.
        rewrite !Znth_sublist in Hoi, Hoj by lia.
        replace (j + 0) with j in Hoi by lia.
        replace (j + 1 + 0) with (j + 1) in Hoj by lia.
        exact (conj Hoi (conj Hoj Hsep)).
      * assert (j = processed - 1) by lia; subst j.
        destruct Hoccupation as [left Hoccupation].
        exists left, endpoint,
          (fst (Znth processed trees (0, 0))),
          (fst (Znth processed trees (0, 0)) + snd (Znth processed trees (0, 0))).
        rewrite app_Znth1 by lia.
        rewrite app_Znth2 by lia.
        replace (processed - 1 + 1 - Zlength choices) with 0 by lia.
        simpl.
        replace (processed - 1 + 1) with processed by lia.
        split; [exact Hoccupation |].
        split.
        -- unfold TreeOccupation. right; right. repeat split; reflexivity.
        -- exact Hendpoint.
Qed.
Lemma FellingCount_append_right__final_general :
  forall choices,
    FellingCount (choices ++ 1 :: nil) = FellingCount choices + 1.
Proof.
  intros choices.
  unfold FellingCount.
  rewrite filter_app.
  simpl.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.
Lemma Zlength_filter_le__final_general :
  forall (A : Type) (f : A -> bool) (l : list A),
    Zlength (filter f l) <= Zlength l.
Proof.
  intros A f l.
  induction l as [|a l IH]; simpl.
  - lia.
  - destruct (f a); simpl; rewrite !Zlength_cons in *; lia.
Qed.
Lemma FellingCount_full_le_prefix__final_general :
  forall choices,
    1 <= Zlength choices ->
    FellingCount choices <=
      FellingCount (sublist 0 (Zlength choices - 1) choices) + 1.
Proof.
  intros choices Hnonempty.
  assert (Hdecomp :
    choices = sublist 0 (Zlength choices - 1) choices ++
      Znth (Zlength choices - 1) choices 0 :: nil).
  {
    assert (Hlast :
      sublist (Zlength choices - 1) (Zlength choices) choices =
        Znth (Zlength choices - 1) choices 0 :: nil).
    {
      replace (Zlength choices) with (Zlength choices - 1 + 1) at 2 by lia.
      apply sublist_single. lia.
    }
    pose proof (sublist_split 0 (Zlength choices)
      (Zlength choices - 1) choices ltac:(lia) ltac:(lia)) as Hsplit.
    rewrite sublist_self in Hsplit by reflexivity.
    rewrite Hlast in Hsplit.
    exact Hsplit.
  }
  rewrite Hdecomp at 1.
  unfold FellingCount.
  rewrite filter_app.
  rewrite Zlength_app.
  assert (Hlast_count :
    Zlength (filter (fun choice => negb (Z.eqb choice 0))
      (Znth (Zlength choices - 1) choices 0 :: nil)) <= 1).
  {
    pose proof (Zlength_filter_le__final_general Z
      (fun choice => negb (Z.eqb choice 0))
      (Znth (Zlength choices - 1) choices 0 :: nil)).
    rewrite Zlength_cons, Zlength_nil in H. lia.
  }
  lia.
Qed.
Lemma PrefixFellingAdmissible_of_valid__final_general :
  forall trees choices processed,
    Pre trees ->
    1 <= processed ->
    processed + 1 = Zlength trees ->
    ValidFelling trees choices ->
    exists endpoint,
      PrefixFellingAdmissible trees processed
        (sublist 0 processed choices) endpoint.
Proof.
  intros trees choices processed Hpre Hprocessed Htree_length Hvalid.
  pose proof Hvalid as Hvalid_full.
  destruct Hvalid as [Hchoice_length [Hall Hadj]].
  specialize (Hadj (processed - 1) ltac:(lia)).
  destruct Hadj as (li & ri & lj & rj & Hoi & Hoj & Hsep).
  exists ri.
  unfold PrefixFellingAdmissible.
  split; [lia |].
  split.
  - apply ValidFelling_prefix__final_general; [lia |].
    exact Hvalid_full.
  - split.
    + exists li.
      rewrite !Znth_sublist by lia.
      replace (processed - 1 + 0) with (processed - 1) by lia.
      exact Hoi.
    + destruct Hpre as [_ [Htree_props _]].
      pose proof (proj1 (Forall_Znth
        (fun p => 1 <= fst p <= 1000000000 /\
          1 <= snd p <= 1000000000) (0, 0) trees)
        Htree_props processed ltac:(lia)) as Hlast_props.
      destruct Hlast_props as [_ [Hlast_height _]].
      replace (processed - 1 + 1) with processed in Hoj by lia.
      eapply Z.lt_le_trans; [exact Hsep |].
      eapply TreeOccupation_left_le_fst__final_general;
        [exact Hlast_height | exact Hoj].
Qed.
Lemma PrefixFellingState_complete__final_general :
  forall trees processed occupied answer,
    Pre trees ->
    processed = Zlength trees - 1 ->
    PrefixFellingState trees processed occupied answer ->
    Spec trees answer.
Proof.
  intros trees processed occupied answer Hpre Hprocessed Hstate.
  unfold PrefixFellingState in Hstate.
  destruct Hstate as (chosen & Hadmissible & Hanswer & Hoptimal).
  destruct Hadmissible as (Hbounds & Hvalid_prefix & Hoccupation & Hendpoint).
  assert (Htree_length : processed + 1 = Zlength trees) by lia.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists (chosen ++ 1 :: nil).
  split.
  - split.
    + eapply ValidFelling_append_right__final_general; eauto; lia.
    + intros competitor Hvalid_competitor.
      pose proof Hvalid_competitor as Hvalid_competitor_copy.
      destruct Hvalid_competitor_copy as [Hcompetitor_length _].
      pose proof Hpre as Hpre_copy.
      destruct Hpre_copy as [Hpre_length _].
      destruct (PrefixFellingAdmissible_of_valid__final_general
        trees competitor processed Hpre ltac:(lia) Htree_length
        Hvalid_competitor) as [competitor_endpoint Hcompetitor_prefix].
      specialize (Hoptimal (sublist 0 processed competitor)
        competitor_endpoint Hcompetitor_prefix).
      destruct Hoptimal as [Hprefix_le _].
      pose proof (FellingCount_full_le_prefix__final_general competitor
        ltac:(lia)) as Hfull_le.
      replace (Zlength competitor - 1) with processed in Hfull_le by lia.
      change (FellingCount competitor <= FellingCount (chosen ++ 1 :: nil)).
      rewrite FellingCount_append_right__final_general.
      lia.
  - change (FellingCount (chosen ++ 1 :: nil) = answer).
    rewrite FellingCount_append_right__final_general.
    lia.
Qed.
Lemma Spec_small_trees__final_small :
  forall trees,
    Pre trees ->
    Zlength trees <= 2 ->
    Spec trees (Zlength trees).
Proof.
  intros trees Hpre Hsmall.
  assert (Hfilter : forall choices : list Z,
      Zlength (filter (fun x => negb (Z.eqb x 0)) choices) <=
      Zlength choices).
  {
    intros choices.
    rewrite !Zlength_correct.
    apply Nat2Z.inj_le.
    apply filter_length_le.
  }
  destruct trees as [| t1 rest].
  - unfold Pre in Hpre.
    rewrite Zlength_nil in Hpre.
    lia.
  - destruct rest as [| t2 rest].
    + unfold Spec, max_value_of_subset, max_object_of_subset.
      exists (cons (-1) nil).
      split.
      * split.
        -- unfold ValidFelling.
           split.
           ++ reflexivity.
           ++ split.
              ** constructor; [lia | constructor].
              ** intros i Hi. simpl in Hi. lia.
        -- intros competitor Hcompetitor.
           destruct Hcompetitor as [Hlength _].
           specialize (Hfilter competitor).
           change (Zlength
             (filter (fun x => negb (Z.eqb x 0)) competitor) <= 1).
           apply Z.le_trans with (m := Zlength competitor).
           ++ exact Hfilter.
           ++ simpl in Hlength.
              rewrite Hlength.
              rewrite Zlength_cons, Zlength_nil.
              lia.
      * reflexivity.
    + destruct rest as [| t3 rest].
      * destruct Hpre as [_ [_ Hmono]].
        assert (Hposition : fst t1 < fst t2).
        {
          specialize (Hmono 0 1 ltac:(lia) ltac:(lia)
            ltac:(change (1 < 2); lia)).
          simpl in Hmono.
          exact Hmono.
        }
        unfold Spec, max_value_of_subset, max_object_of_subset.
        exists (cons (-1) (cons 1 nil)).
        split.
        -- split.
           ++ unfold ValidFelling.
              split.
              ** reflexivity.
              ** split.
                 --- constructor; [lia | constructor; [lia | constructor]].
                 --- intros i Hi.
                     assert (i = 0) by (simpl in Hi; lia).
                     subst i.
                     exists (fst t1 - snd t1), (fst t1),
                       (fst t2), (fst t2 + snd t2).
                     split.
                     +++ left. simpl. repeat split; reflexivity.
                     +++ split.
                         *** right. right. simpl. repeat split; reflexivity.
                         *** exact Hposition.
           ++ intros competitor Hcompetitor.
              destruct Hcompetitor as [Hlength _].
              specialize (Hfilter competitor).
              change (Zlength
                (filter (fun x => negb (Z.eqb x 0)) competitor) <= 2).
              apply Z.le_trans with (m := Zlength competitor).
              ** exact Hfilter.
              ** simpl in Hlength.
                 rewrite Hlength.
                 rewrite !Zlength_cons, Zlength_nil.
                 lia.
        -- reflexivity.
      * rewrite !Zlength_cons in Hsmall.
        pose proof (Zlength_nonneg rest).
        lia.
Qed.
