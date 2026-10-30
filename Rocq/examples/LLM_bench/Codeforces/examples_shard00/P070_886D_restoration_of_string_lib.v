Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Import ListNotations.

Definition LowercaseLetter (c : Z) : Prop := 97 <= c <= 122.

Definition Pre (given : list (list Z)) : Prop :=
  1 <= Zlength given <= 100000 /\
  Forall (fun word =>
    0 < Zlength word <= 100000 /\
    Forall LowercaseLetter word) given.

Definition OccursContiguously (word text : list Z) : Prop :=
  exists before after, text = before ++ word ++ after.

Definition GoodRestoration (given : list (list Z)) (text : list Z) : Prop :=
  NoDup text /\
  (forall c,
    In c text <-> exists word, In word given /\ In c word) /\
  (forall word, In word given -> OccursContiguously word text).

Definition Spec (given : list (list Z)) (out : option (list Z)) : Prop :=
  match out with
  | Some text => GoodRestoration given text
  | None => forall text, ~ GoodRestoration given text
  end.

Definition BoundedGraphArray (values : list Z) : Prop :=
  Zlength values = 26 /\
  forall k, 0 <= k < 26 -> -1 <= Znth k values (-1) < 26.

Definition BooleanArray (values : list Z) : Prop :=
  Zlength values = 26 /\
  forall k, 0 <= k < 26 -> Znth k values 0 = 0 \/ Znth k values 0 = 1.

Definition AllMinusOne (values : list Z) : Prop :=
  forall k, 0 <= k < Zlength values -> Znth k values (-1) = -1.

Definition AllZero (values : list Z) : Prop :=
  forall k, 0 <= k < Zlength values -> Znth k values 0 = 0.

Definition UsedInWords (words : list (list Z)) (c : Z) : Prop :=
  exists word, In word words /\ In c word.

Definition AdjacentInWords
    (words : list (list Z)) (left right : Z) : Prop :=
  exists word i,
    In word words /\
    0 <= i /\ i + 1 < Zlength word /\
    Znth i word 0 = left /\ Znth (i + 1) word 0 = right.

Definition CompatibleWords (words : list (list Z)) : Prop :=
  (forall word, In word words -> NoDup word) /\
  (forall left right1 right2,
    AdjacentInWords words left right1 ->
    AdjacentInWords words left right2 -> right1 = right2) /\
  (forall left1 left2 right,
    AdjacentInWords words left1 right ->
    AdjacentInWords words left2 right -> left1 = left2).

Definition EncodesGraph
    (words : list (list Z))
    (next prev used : list Z) : Prop :=
  CompatibleWords words /\
  BoundedGraphArray next /\
  BoundedGraphArray prev /\
  BooleanArray used /\
  (forall c, 0 <= c < 26 ->
    (Znth c used 0 = 1 <-> UsedInWords words (97 + c))) /\
  (forall left right, 0 <= left < 26 -> 0 <= right < 26 ->
    (Znth left next (-1) = right <->
      AdjacentInWords words (97 + left) (97 + right))) /\
  (forall left right, 0 <= left < 26 -> 0 <= right < 26 ->
    (Znth right prev (-1) = left <->
      AdjacentInWords words (97 + left) (97 + right))).

Definition InitState
    (next_prefix prev_prefix used : list Z) : Prop :=
  Zlength next_prefix = Zlength prev_prefix /\
  AllMinusOne next_prefix /\
  AllMinusOne prev_prefix /\
  BooleanArray used /\ AllZero used.

Definition GraphBuildState
    (given : list (list Z)) (words_done : Z)
    (next prev used : list Z) : Prop :=
  Pre given /\
  EncodesGraph (sublist 0 words_done given) next prev used.

Definition WordScanState
    (given : list (list Z)) (word_index scanned : Z)
    (next prev used seen : list Z) (last : Z) : Prop :=
  let word := Znth word_index given [] in
  Pre given /\
  EncodesGraph
    (sublist 0 word_index given ++ [sublist 0 scanned word])
    next prev used /\
  BooleanArray seen /\
  (forall c, 0 <= c < 26 ->
    (Znth c seen 0 = 1 <-> In (97 + c) (sublist 0 scanned word))) /\
  (scanned = 0 /\ last = -1 \/
   0 < scanned /\ last = Znth (scanned - 1) word 0 - 97).

Inductive NextReach (next : list Z) : Z -> Z -> Prop :=
| next_reach_refl : forall c, NextReach next c c
| next_reach_step : forall from mid to,
    Znth from next (-1) = mid ->
    0 <= mid < 26 ->
    NextReach next mid to ->
    NextReach next from to.

Definition IsHead
    (prev used : list Z) (c : Z) : Prop :=
  0 <= c < 26 /\ Znth c used 0 = 1 /\ Znth c prev (-1) = -1.

Definition CompletedHeadSet
    (next prev used : list Z) (heads_done : Z) (visited : list Z) : Prop :=
  BooleanArray visited /\
  forall c, 0 <= c < 26 ->
    (Znth c visited 0 = 1 <->
      exists head,
        0 <= head < heads_done /\
        IsHead prev used head /\ NextReach next head c).

Definition OutputMatchesVisited
    (visited output : list Z) : Prop :=
  NoDup output /\
  (forall c, 0 <= c < 26 ->
    (Znth c visited 0 = 1 <-> In (97 + c) output)).

Inductive PathPrefix (next : list Z) (start : Z) : list Z -> Z -> Prop :=
| path_prefix_start : PathPrefix next start [] start
| path_prefix_step : forall path current successor,
    PathPrefix next start path current ->
    0 <= current < 26 ->
    Znth current next (-1) = successor ->
    PathPrefix next start (path ++ [current]) successor.

Definition MarkedPath
    (before path after : list Z) : Prop :=
  BooleanArray before /\ BooleanArray after /\
  forall c, 0 <= c < 26 ->
    (Znth c after 0 = 1 <->
      Znth c before 0 = 1 \/ In c path).

Inductive OrderedTraversal
    (next prev used : list Z) : Z -> list Z -> Prop :=
| ordered_traversal_zero : OrderedTraversal next prev used 0 []
| ordered_traversal_skip : forall bound output,
    OrderedTraversal next prev used bound output ->
    0 <= bound < 26 ->
    ~ IsHead prev used bound ->
    OrderedTraversal next prev used (bound + 1) output
| ordered_traversal_head : forall bound output path,
    OrderedTraversal next prev used bound output ->
    0 <= bound < 26 ->
    IsHead prev used bound ->
    PathPrefix next bound path (-1) ->
    OrderedTraversal next prev used (bound + 1)
      (output ++ map (fun c => 97 + c) path).

Definition TraversalState
    (next prev used : list Z) (heads_done : Z)
    (visited output : list Z) : Prop :=
  CompletedHeadSet next prev used heads_done visited /\
  OutputMatchesVisited visited output /\
  OrderedTraversal next prev used heads_done output.

Definition PathScanState
    (next prev used : list Z) (start current : Z)
    (visited output : list Z) : Prop :=
  exists visited_before output_before path,
    TraversalState next prev used start visited_before output_before /\
    IsHead prev used start /\
    PathPrefix next start path current /\
    MarkedPath visited_before path visited /\
    output = output_before ++ map (fun c => 97 + c) path /\
    (current = -1 \/
      (0 <= current < 26 /\ Znth current visited 0 = 0)).

Definition CoverageScanState
    (used visited : list Z) (checked : Z) : Prop :=
  BooleanArray used /\ BooleanArray visited /\
  forall c, 0 <= c < checked ->
    Znth c used 0 = 1 -> Znth c visited 0 = 1.

Definition SuccessfulTraversal
    (given : list (list Z))
    (next prev used visited output : list Z) : Prop :=
  EncodesGraph given next prev used /\
  TraversalState next prev used 26 visited output /\
  CoverageScanState used visited 26 /\
  GoodRestoration given output.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
From Coq Require Import Lia.
Lemma repeat_zero_state__initialization_and_row_frame :
  BooleanArray (repeat 0 (Z.to_nat 26)) /\
  AllZero (repeat 0 (Z.to_nat 26)).
Proof.
  split.
  - unfold BooleanArray.
    split.
    + rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      reflexivity.
    + intros k Hk. left. apply Znth_repeat.
  - unfold AllZero.
    intros k Hk. apply Znth_repeat.
Qed.
Lemma init_state_append_minus_one__initialization_and_row_frame :
  forall next prev used,
    InitState next prev used ->
    InitState (next ++ [-1]) (prev ++ [-1]) used.
Proof.
  intros next prev used Hinit.
  unfold InitState in *.
  destruct Hinit as [Hlen [Hnext [Hprev Hused]]].
  split.
  - rewrite !Zlength_app_cons. lia.
  - split.
    + unfold AllMinusOne in *. intros k Hk.
    rewrite Zlength_app_cons in Hk.
    destruct (Z_lt_ge_dec k (Zlength next)).
    * rewrite app_Znth1 by lia. apply Hnext. lia.
    * assert (k = Zlength next) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (Zlength next - Zlength next) with 0 by lia.
      reflexivity.
    + split.
      * unfold AllMinusOne in *. intros k Hk.
        rewrite Zlength_app_cons in Hk.
        destruct (Z_lt_ge_dec k (Zlength prev)).
        -- rewrite app_Znth1 by lia. apply Hprev. lia.
        -- assert (k = Zlength prev) by lia. subst k.
           rewrite app_Znth2 by lia.
           replace (Zlength prev - Zlength prev) with 0 by lia.
           reflexivity.
      * exact Hused.
Qed.
Lemma encodes_graph_empty_from_init__initialization_and_row_frame :
  forall next prev used,
    Zlength next = 26 ->
    Zlength prev = 26 ->
    InitState next prev used ->
    EncodesGraph [] next prev used.
Proof.
  intros next prev used Hnextlen Hprevlen Hinit.
  unfold InitState in Hinit.
  destruct Hinit as [_ [Hnextminus [Hprevminus [Hbool Hzero]]]].
  unfold EncodesGraph.
  split.
  - unfold CompatibleWords. split.
    + intros word Hin. contradiction.
    + split.
      * intros left right1 right2 H1. unfold AdjacentInWords in H1.
        destruct H1 as (word & idx & Hin & _). contradiction.
      * intros left1 left2 right H1. unfold AdjacentInWords in H1.
        destruct H1 as (word & idx & Hin & _). contradiction.
  - split.
    + unfold BoundedGraphArray. split.
      * exact Hnextlen.
      * intros k Hk. rewrite Hnextminus by (rewrite Hnextlen; lia). lia.
    + split.
      * unfold BoundedGraphArray. split.
        -- exact Hprevlen.
        -- intros k Hk. rewrite Hprevminus by (rewrite Hprevlen; lia). lia.
      * split.
        -- exact Hbool.
        -- split.
           ++ intros c Hc. split.
              ** intro Hone. rewrite Hzero in Hone by (destruct Hbool; lia). lia.
              ** unfold UsedInWords. intros (word & Hin & _). contradiction.
           ++ split.
              ** intros left right Hleft Hright. split.
                 --- intro Hedge.
                     rewrite Hnextminus in Hedge by (rewrite Hnextlen; lia). lia.
                 --- unfold AdjacentInWords.
                     intros (word & idx & Hin & _). contradiction.
              ** intros left right Hleft Hright. split.
                 --- intro Hedge.
                     rewrite Hprevminus in Hedge by (rewrite Hprevlen; lia). lia.
                 --- unfold AdjacentInWords.
                     intros (word & idx & Hin & _). contradiction.
Qed.
Lemma encodes_graph_append_empty__initialization_and_row_frame :
  forall words next prev used,
    EncodesGraph words next prev used ->
    EncodesGraph (words ++ [[]]) next prev used.
Proof.
  intros words next prev used Henc.
  assert (Hused : forall c,
      UsedInWords (words ++ [[]]) c <-> UsedInWords words c).
  {
    intro c. unfold UsedInWords. split.
    - intros (word & Hin & Hinc).
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + exists word. auto.
      + simpl in Hin. destruct Hin as [Heq | []]. subst word.
        contradiction.
    - intros (word & Hin & Hinc). exists word. split; auto.
      apply in_or_app. left. exact Hin.
  }
  assert (Hadj : forall left right,
      AdjacentInWords (words ++ [[]]) left right <->
      AdjacentInWords words left right).
  {
    intros left right. unfold AdjacentInWords. split.
    - intros (word & i & Hin & Hi & Hij & Hleft & Hright).
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + exists word, i. auto.
      + simpl in Hin. destruct Hin as [Heq | []]. subst word.
        rewrite Zlength_nil in Hij. lia.
    - intros (word & i & Hin & Hi & Hij & Hleft & Hright).
      exists word, i. repeat split; auto.
      apply in_or_app. left. exact Hin.
  }
  unfold EncodesGraph in *.
  destruct Henc as
    [Hcompat [Hnext [Hprev [Hbool [Husediff [Hnextiff Hpreviff]]]]]].
  split.
  - unfold CompatibleWords in *.
    destruct Hcompat as [Hnodup [Hout Hin]].
    split.
    + intros word Hword. apply in_app_or in Hword.
      destruct Hword as [Hword | Hword].
      * apply Hnodup. exact Hword.
      * destruct Hword as [Hword | Hword].
        -- rewrite <- Hword. constructor.
        -- contradiction.
    + split.
      * intros left right1 right2 H1 H2.
        apply (Hout left right1 right2).
        -- apply (proj1 (Hadj left right1)). exact H1.
        -- apply (proj1 (Hadj left right2)). exact H2.
      * intros left1 left2 right H1 H2.
        apply (Hin left1 left2 right).
        -- apply (proj1 (Hadj left1 right)). exact H1.
        -- apply (proj1 (Hadj left2 right)). exact H2.
  - split.
    + exact Hnext.
    + split.
      * exact Hprev.
      * split.
        -- exact Hbool.
        -- split.
           ++ intros c Hc. rewrite Hused. apply Husediff. exact Hc.
           ++ split.
              ** intros left right Hleft Hright.
                 rewrite Hadj. apply Hnextiff; assumption.
              ** intros left right Hleft Hright.
                 rewrite Hadj. apply Hpreviff; assumption.
Qed.
Lemma word_scan_state_zero__initialization_and_row_frame :
  forall given z next prev used,
    GraphBuildState given z next prev used ->
    WordScanState given z 0 next prev used
      (repeat 0 (Z.to_nat 26)) (-1).
Proof.
  intros given z next prev used Hgraph.
  unfold GraphBuildState in Hgraph.
  destruct Hgraph as [Hpre Henc].
  unfold WordScanState.
  split.
  - exact Hpre.
  - split.
    + unfold sublist at 2. simpl.
      apply encodes_graph_append_empty__initialization_and_row_frame.
      exact Henc.
    + split.
      * apply repeat_zero_state__initialization_and_row_frame.
      * split.
        -- intros c Hc. unfold sublist. simpl.
           change (Znth c (repeat 0 (Z.to_nat 26)) 0 = 1 <-> False).
           rewrite Znth_repeat. split; intro H; [discriminate | contradiction].
        -- left. auto.
Qed.
Lemma used_in_words_extend__word_scan_steps :
  forall base prefix ch c,
    UsedInWords (base ++ [prefix ++ [ch]]) c <->
    UsedInWords (base ++ [prefix]) c \/ c = ch.
Proof.
  intros base prefix ch c. unfold UsedInWords.
  split.
  - intros (word & Hin & Hc).
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. exists word. split; [apply in_or_app; left; exact Hin|exact Hc].
    + simpl in Hin. destruct Hin as [Heq | []]. subst word.
      apply in_app_or in Hc. destruct Hc as [Hc | Hc].
      * left. exists prefix. split; [apply in_or_app; right; simpl; auto|exact Hc].
      * simpl in Hc. destruct Hc as [-> | []]. right. reflexivity.
  - intros [(word & Hin & Hc) | ->].
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exists word. split; [apply in_or_app; left; exact Hin|exact Hc].
      * simpl in Hin. destruct Hin as [Heq | []]. subst word.
        exists (prefix ++ [ch]). split.
        -- apply in_or_app. right. simpl. auto.
        -- apply in_or_app. left. exact Hc.
    + exists (prefix ++ [ch]). split.
      * apply in_or_app. right. simpl. auto.
      * apply in_or_app. right. simpl. auto.
Qed.
Lemma adjacent_in_words_extend__word_scan_steps :
  forall base prefix ch tail left right,
    0 < Zlength prefix ->
    Znth (Zlength prefix - 1) prefix 0 = tail ->
    (AdjacentInWords (base ++ [prefix ++ [ch]]) left right <->
     AdjacentInWords (base ++ [prefix]) left right \/
     (left = tail /\ right = ch)).
Proof.
  intros base prefix ch tail left right Hprefix Htail.
  unfold AdjacentInWords. split.
  - intros (word & j & Hin & Hj & Hjlen & Hleft & Hright).
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + left. exists word, j. repeat split; try assumption.
      apply in_or_app. left. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | []]. subst word.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hjlen.
      assert (j + 1 < Zlength prefix \/ j + 1 = Zlength prefix) as Hcase by lia.
      destruct Hcase as [Hold | Hnew].
      * left. exists prefix, j. repeat split; try assumption.
        -- apply in_or_app. right. simpl. auto.
        -- rewrite app_Znth1 in Hleft by lia. exact Hleft.
        -- rewrite app_Znth1 in Hright by lia. exact Hright.
      * right. split.
        -- assert (j = Zlength prefix - 1) by lia. subst j.
           rewrite app_Znth1 in Hleft by lia.
           rewrite Htail in Hleft. lia.
        -- rewrite app_Znth2 in Hright by lia.
           replace (j + 1 - Zlength prefix) with 0 in Hright by lia.
           simpl in Hright. symmetry. exact Hright.
  - intros [Hold | [-> ->]].
    + destruct Hold as (word & j & Hin & Hj & Hjlen & Hleft & Hright).
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exists word, j. repeat split; try assumption.
        apply in_or_app. left. exact Hin.
      * simpl in Hin. destruct Hin as [Heq | []]. subst word.
        exists (prefix ++ [ch]), j. repeat split; try assumption.
        -- apply in_or_app. right. simpl. auto.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
        -- rewrite app_Znth1 by lia. exact Hleft.
        -- rewrite app_Znth1 by lia. exact Hright.
    + exists (prefix ++ [ch]), (Zlength prefix - 1).
      repeat split.
      * apply in_or_app. right. simpl. auto.
      * lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * rewrite app_Znth1 by lia. exact Htail.
      * rewrite app_Znth2 by lia.
        replace (Zlength prefix - 1 + 1 - Zlength prefix) with 0 by lia.
        reflexivity.
Qed.
Lemma replace_Znth_Zlength__word_scan_steps :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [|a l IH]; simpl in *; intros; auto.
  unfold replace_Znth in *. destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma boolean_array_replace_one__word_scan_steps :
  forall values k,
    BooleanArray values -> 0 <= k < 26 ->
    BooleanArray (replace_Znth k 1 values).
Proof.
  intros values k [Hlen Hvalues] Hk. split.
  - rewrite replace_Znth_Zlength__word_scan_steps. exact Hlen.
  - intros j Hj. destruct (Z.eq_dec j k) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia. auto.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hvalues. exact Hj.
Qed.
Lemma encodes_graph_extend_existing__word_scan_steps :
  forall base prefix ch tail next prev used,
    0 < Zlength prefix ->
    Znth (Zlength prefix - 1) prefix 0 = tail ->
    EncodesGraph (base ++ [prefix]) next prev used ->
    AdjacentInWords (base ++ [prefix]) tail ch ->
    ~ In ch prefix ->
    EncodesGraph (base ++ [prefix ++ [ch]]) next prev used.
Proof.
  intros base prefix ch tail next prev used Hprefix Htail Henc Hedge Hfresh.
  destruct Henc as [Hcompat [Hnext [Hprev [Hused [Husediff [Hnextiff Hpreviff]]]]]].
  split.
  - destruct Hcompat as [Hnodup [Hout Hin]]. repeat split.
    + intros word Hword. apply in_app_or in Hword. destruct Hword as [Hword | Hword].
      * apply Hnodup. apply in_or_app. left. exact Hword.
      * simpl in Hword. destruct Hword as [Heq | []]. subst word.
        apply NoDup_app. repeat split.
        -- apply Hnodup. apply in_or_app. right. simpl. auto.
        -- constructor. { simpl; auto. } constructor.
        -- intros x Hx Hxch. simpl in Hxch. destruct Hxch as [-> | []].
           contradiction.
    + intros l r1 r2 H1 H2.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix ch tail l r1 Hprefix Htail)) in H1.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix ch tail l r2 Hprefix Htail)) in H2.
      destruct H1 as [H1 | [Hl1 Hr1]]; destruct H2 as [H2 | [Hl2 Hr2]].
      * eapply Hout; eauto.
      * subst l r2. eapply Hout; eauto.
      * subst l r1. symmetry. eapply Hout; eauto.
      * congruence.
    + intros l1 l2 r H1 H2.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix ch tail l1 r Hprefix Htail)) in H1.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix ch tail l2 r Hprefix Htail)) in H2.
      destruct H1 as [H1 | [Hl1 Hr1]]; destruct H2 as [H2 | [Hl2 Hr2]].
      * eapply Hin; eauto.
      * subst l2 r. eapply Hin; eauto.
      * subst l1 r. symmetry. eapply Hin; eauto.
      * congruence.
  - split; [exact Hnext|].
    split; [exact Hprev|].
    split; [exact Hused|].
    split.
    + intros c Hc. rewrite Husediff by exact Hc.
      rewrite used_in_words_extend__word_scan_steps.
      split; [auto|]. intros [Hold | Heq]; [exact Hold|].
      subst ch. unfold AdjacentInWords in Hedge.
      destruct Hedge as (word & j & Hword & Hj & Hjlen & Hleft & Hright).
      unfold UsedInWords. exists word. split; [exact Hword|].
      unfold Znth in Hright. rewrite <- Hright. apply nth_In.
      rewrite Zlength_correct in Hjlen. lia.
    + split.
      * intros l r Hl Hr. split; intro Hval.
        -- apply (proj2 (adjacent_in_words_extend__word_scan_steps
             base prefix ch tail (97 + l) (97 + r) Hprefix Htail)).
           left. apply (proj1 (Hnextiff l r Hl Hr)). exact Hval.
        -- apply (proj2 (Hnextiff l r Hl Hr)).
           apply (proj1 (adjacent_in_words_extend__word_scan_steps
             base prefix ch tail (97 + l) (97 + r) Hprefix Htail)) in Hval.
           destruct Hval as [Hold | [Heql Heqr]]; [exact Hold|].
           rewrite <- Heql, <- Heqr in Hedge. exact Hedge.
      * intros l r Hl Hr. split; intro Hval.
        -- apply (proj2 (adjacent_in_words_extend__word_scan_steps
             base prefix ch tail (97 + l) (97 + r) Hprefix Htail)).
           left. apply (proj1 (Hpreviff l r Hl Hr)). exact Hval.
        -- apply (proj2 (Hpreviff l r Hl Hr)).
           apply (proj1 (adjacent_in_words_extend__word_scan_steps
             base prefix ch tail (97 + l) (97 + r) Hprefix Htail)) in Hval.
           destruct Hval as [Hold | [Heql Heqr]]; [exact Hold|].
           rewrite <- Heql, <- Heqr in Hedge. exact Hedge.
Qed.
Lemma word_scan_step_existing_edge__word_scan_steps :
  forall given z i next prev used seen last x,
    0 <= i < Zlength (Znth z given []) ->
    0 <= last < 26 -> 0 <= x < 26 ->
    WordScanState given z i next prev used seen last ->
    Znth i (Znth z given []) 0 = 97 + x ->
    Znth last next (-1) = x ->
    Znth x prev (-1) = last ->
    Znth x seen 0 = 0 ->
    WordScanState given z (i + 1)
      (replace_Znth last x next) (replace_Znth x last prev)
      (replace_Znth x 1 used) (replace_Znth x 1 seen) x.
Proof.
  intros given z i next prev used seen last x Hi Hlast Hx Hstate Hchar
    Hnext Hprev Hseen.
  unfold WordScanState in Hstate |- *. fold (Znth z given []) in *.
  destruct Hstate as [Hpre [Henc [Hseenbool [Hseeniff Hlaststate]]]].
  destruct Hseenbool as [Hseenlen Hseenvals].
  set (word := Znth z given []) in *.
  set (base := sublist 0 z given) in *.
  set (prefix := sublist 0 i word) in *.
  assert (Hprefixlen : Zlength prefix = i).
  { unfold prefix. rewrite Zlength_sublist by lia. lia. }
  assert (Hprefixpos : 0 < Zlength prefix).
  { destruct Hlaststate as [[Hz Hminus] | [Hpos Hlastold]]; [lia|].
    rewrite Hprefixlen. lia. }
  assert (Htail : Znth (Zlength prefix - 1) prefix 0 = 97 + last).
  { destruct Hlaststate as [[Hz Hminus] | [Hpos Hlastold]]; [lia|].
    rewrite Hprefixlen. unfold prefix.
    rewrite (@Znth_sublist0 Z 0 (i - 1) i word) by lia. lia. }
  assert (Hfresh : ~ In (97 + x) prefix).
  { intro Hin. apply (proj2 (Hseeniff x Hx)) in Hin. congruence. }
  assert (Hedge : AdjacentInWords (base ++ [prefix]) (97 + last) (97 + x)).
  { unfold EncodesGraph in Henc.
    destruct Henc as (_ & _ & _ & _ & _ & Hnextiff & _).
    apply (proj1 (Hnextiff last x Hlast Hx)). exact Hnext. }
  assert (Hencnew : EncodesGraph (base ++ [prefix ++ [97 + x]]) next prev used).
  { eapply encodes_graph_extend_existing__word_scan_steps; eauto. }
  assert (Husedx : Znth x used 0 = 1).
  { unfold EncodesGraph in Henc.
    destruct Henc as (_ & _ & _ & _ & Husediff & _).
    apply (proj2 (Husediff x Hx)).
    unfold AdjacentInWords in Hedge.
    destruct Hedge as (w & j & Hw & Hj & Hjlen & Hjl & Hjr).
    unfold UsedInWords. exists w. split; [exact Hw|].
    unfold Znth in Hjr. rewrite <- Hjr. apply nth_In.
    rewrite Zlength_correct in Hjlen. lia. }
  assert (Hnextrep : replace_Znth last x next = next).
  { rewrite <- Hnext. apply replace_Znth_Znth. }
  assert (Hprevrep : replace_Znth x last prev = prev).
  { rewrite <- Hprev. apply replace_Znth_Znth. }
  assert (Husedrep : replace_Znth x 1 used = used).
  { rewrite <- Husedx. apply replace_Znth_Znth. }
  rewrite Hnextrep, Hprevrep, Husedrep.
  split; [exact Hpre|]. split.
  - assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
    { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
      rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
    rewrite Hprefixeq. exact Hencnew.
  - split.
    + apply boolean_array_replace_one__word_scan_steps; [split; assumption|assumption].
    + split.
      * intros c Hc. destruct (Z.eq_dec c x) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by lia.
           split; intro; [|reflexivity].
           assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
           { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
             rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
           rewrite Hprefixeq. apply in_or_app. right. simpl. auto.
        -- rewrite Znth_replace_Znth_Diff by lia.
           rewrite Hseeniff by exact Hc.
           assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
           { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
             rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
           rewrite Hprefixeq. split.
           ++ intro Hin. apply in_or_app. left. exact Hin.
           ++ intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact Hin|].
              change (97 + x = 97 + c \/ False) in Hin.
              destruct Hin as [Heq | []].
              exfalso. apply Hneq. symmetry. apply (Z.add_reg_l 97). exact Heq.
      * right. split; [lia|]. replace (i + 1 - 1) with i by lia.
        rewrite Hchar. lia.
Qed.
Lemma adjacent_singleton_equiv__word_scan_steps :
  forall base ch left right,
    AdjacentInWords (base ++ [[ch]]) left right <->
    AdjacentInWords (base ++ [[]]) left right.
Proof.
  intros base ch left right. unfold AdjacentInWords. split.
  - intros (word & j & Hin & Hj & Hjlen & Hleft & Hright).
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + exists word, j. repeat split; try assumption.
      apply in_or_app. left. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | []]. subst word.
      rewrite Zlength_cons, Zlength_nil in Hjlen. lia.
  - intros (word & j & Hin & Hj & Hjlen & Hleft & Hright).
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + exists word, j. repeat split; try assumption.
      apply in_or_app. left. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | []]. subst word.
      rewrite Zlength_nil in Hjlen. lia.
Qed.
Lemma encodes_graph_add_first_char__word_scan_steps :
  forall base ch x next prev used,
    ch = 97 + x -> 0 <= x < 26 ->
    EncodesGraph (base ++ [[]]) next prev used ->
    EncodesGraph (base ++ [[ch]]) next prev (replace_Znth x 1 used).
Proof.
  intros base ch x next prev used Hch Hx Henc. subst ch.
  destruct Henc as [Hcompat [Hnext [Hprev [Hused [Husediff [Hnextiff Hpreviff]]]]]].
  split.
  - destruct Hcompat as [Hnodup [Hout Hin]]. repeat split.
    + intros word Hword. apply in_app_or in Hword. destruct Hword as [Hword | Hword].
      * apply Hnodup. apply in_or_app. left. exact Hword.
      * simpl in Hword. destruct Hword as [Heq | []]. subst word.
        constructor. { simpl; auto. } constructor.
    + intros l r1 r2 H1 H2. eapply Hout.
      * apply (proj1 (adjacent_singleton_equiv__word_scan_steps base (97 + x) l r1)). exact H1.
      * apply (proj1 (adjacent_singleton_equiv__word_scan_steps base (97 + x) l r2)). exact H2.
    + intros l1 l2 r H1 H2. eapply Hin.
      * apply (proj1 (adjacent_singleton_equiv__word_scan_steps base (97 + x) l1 r)). exact H1.
      * apply (proj1 (adjacent_singleton_equiv__word_scan_steps base (97 + x) l2 r)). exact H2.
  - split; [exact Hnext|]. split; [exact Hprev|].
    split.
    + apply boolean_array_replace_one__word_scan_steps; assumption.
    + split.
      * intros c Hc. destruct (Z.eq_dec c x) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by (destruct Hused; lia).
           split; intro; [|reflexivity].
           unfold UsedInWords. exists [97 + x]. split.
           ++ apply in_or_app. right. simpl. auto.
           ++ simpl. auto.
        -- rewrite Znth_replace_Znth_Diff by (destruct Hused; lia).
           split; intro Hval.
           ++ apply (proj2 (used_in_words_extend__word_scan_steps
                base [] (97 + x) (97 + c))).
              left. apply (proj1 (Husediff c Hc)). exact Hval.
           ++ apply (proj2 (Husediff c Hc)).
              apply (proj1 (used_in_words_extend__word_scan_steps
                base [] (97 + x) (97 + c))) in Hval.
              destruct Hval as [Hold | Heq]; [exact Hold|].
              exfalso. apply Hneq. apply (Z.add_reg_l 97). exact Heq.
      * split.
        -- intros l r Hl Hr. rewrite Hnextiff by assumption.
           symmetry. apply adjacent_singleton_equiv__word_scan_steps.
        -- intros l r Hl Hr. rewrite Hpreviff by assumption.
           symmetry. apply adjacent_singleton_equiv__word_scan_steps.
Qed.
Lemma word_scan_step_first_char__word_scan_steps :
  forall given z next prev used seen x,
    0 <= z < Zlength given ->
    0 <= x < 26 ->
    WordScanState given z 0 next prev used seen (-1) ->
    Znth 0 (Znth z given []) 0 = 97 + x ->
    Znth x seen 0 = 0 ->
    WordScanState given z 1 next prev
      (replace_Znth x 1 used) (replace_Znth x 1 seen) x.
Proof.
  intros given z next prev used seen x Hz Hx Hstate Hchar Hseen.
  unfold WordScanState in Hstate |- *. fold (Znth z given []) in *.
  destruct Hstate as [Hpre [Henc [Hseenbool [Hseeniff Hlaststate]]]].
  destruct Hseenbool as [Hseenlen Hseenvals].
  set (word := Znth z given []) in *.
  set (base := sublist 0 z given) in *.
  assert (Hempty : sublist 0 0 word = []).
  { reflexivity. }
  rewrite Hempty in Henc.
  split; [exact Hpre|]. split.
  - assert (Hone : sublist 0 1 word = [97 + x]).
    { replace 1 with (0 + 1) by lia.
      rewrite (@sublist_single Z 0 0 word).
      - rewrite Hchar. reflexivity.
      - destruct Hpre as [Hgivenlen Hwords].
        assert (0 < Zlength word).
        { apply Forall_forall with (x := word) in Hwords.
          - tauto.
          - unfold word, Znth. apply nth_In.
            rewrite Zlength_correct in Hz. lia. }
        lia. }
    rewrite Hone. apply encodes_graph_add_first_char__word_scan_steps with (x := x); auto.
  - split.
    + apply boolean_array_replace_one__word_scan_steps; [split; assumption|assumption].
    + split.
      * intros c Hc. destruct (Z.eq_dec c x) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by lia. split; intro; [|reflexivity].
           assert (Hone : sublist 0 1 word = [97 + x]).
           { replace 1 with (0 + 1) by lia.
             rewrite (@sublist_single Z 0 0 word).
             - rewrite Hchar. reflexivity.
             - unfold Pre in Hpre. destruct Hpre as [Hgivenlen Hwords].
               apply Forall_forall with (x := word) in Hwords.
               ++ destruct Hwords as [[Hpos Hbound] Hletters]. lia.
               ++ unfold word, Znth. apply nth_In.
                  rewrite Zlength_correct in Hz. lia. }
           rewrite Hone. simpl. auto.
        -- rewrite Znth_replace_Znth_Diff by lia.
           rewrite Hseeniff by exact Hc. rewrite Hempty.
           assert (Hone : sublist 0 1 word = [97 + x]).
           { replace 1 with (0 + 1) by lia.
             rewrite (@sublist_single Z 0 0 word).
             - rewrite Hchar. reflexivity.
             - unfold Pre in Hpre. destruct Hpre as [Hgivenlen Hwords].
               apply Forall_forall with (x := word) in Hwords.
               ++ destruct Hwords as [[Hpos Hbound] Hletters]. lia.
               ++ unfold word, Znth. apply nth_In.
                  rewrite Zlength_correct in Hz. lia. }
           rewrite Hone. split; intro Hin.
           ++ contradiction.
           ++ change (97 + x = 97 + c \/ False) in Hin.
              destruct Hin as [Heq | []]. exfalso. apply Hneq.
              symmetry. apply (Z.add_reg_l 97). exact Heq.
      * right. split; [lia|]. replace (1 - 1) with 0 by lia. rewrite Hchar. lia.
Qed.
Lemma adjacent_letters_used__word_scan_steps :
  forall words left right,
    AdjacentInWords words left right ->
    UsedInWords words left /\ UsedInWords words right.
Proof.
  intros words left right (word & j & Hin & Hj & Hjlen & Hleft & Hright).
  split; unfold UsedInWords; exists word; split; [exact Hin| |exact Hin|].
  - unfold Znth in Hleft. rewrite <- Hleft. apply nth_In.
    rewrite Zlength_correct in Hjlen. lia.
  - unfold Znth in Hright. rewrite <- Hright. apply nth_In.
    rewrite Zlength_correct in Hjlen. lia.
Qed.
Lemma encodes_graph_extend_new__word_scan_steps :
  forall base prefix next prev used last x,
    0 < Zlength prefix ->
    Znth (Zlength prefix - 1) prefix 0 = 97 + last ->
    0 <= last < 26 -> 0 <= x < 26 ->
    EncodesGraph (base ++ [prefix]) next prev used ->
    Znth last next (-1) = -1 ->
    Znth x prev (-1) = -1 ->
    ~ In (97 + x) prefix ->
    (forall c, UsedInWords (base ++ [prefix]) c -> 97 <= c <= 122) ->
    EncodesGraph (base ++ [prefix ++ [97 + x]])
      (replace_Znth last x next) (replace_Znth x last prev)
      (replace_Znth x 1 used).
Proof.
  intros base prefix next prev used last x Hprefix Htail Hlast Hx Henc
    Hnextempty Hprevempty Hfresh Hlower.
  destruct Henc as [Hcompat [Hnext [Hprev [Hused [Husediff [Hnextiff Hpreviff]]]]]].
  assert (Hnoout : forall r, AdjacentInWords (base ++ [prefix]) (97 + last) r -> False).
  { intros r Hadj. destruct (adjacent_letters_used__word_scan_steps _ _ _ Hadj) as [_ Hrused].
    specialize (Hlower r Hrused).
    assert (Hr : 0 <= r - 97 < 26) by lia.
    assert (Hedge : Znth last next (-1) = r - 97).
    { apply (proj2 (Hnextiff last (r - 97) Hlast Hr)).
      replace (97 + (r - 97)) with r by lia. exact Hadj. }
    lia. }
  assert (Hnoin : forall l, AdjacentInWords (base ++ [prefix]) l (97 + x) -> False).
  { intros l Hadj. destruct (adjacent_letters_used__word_scan_steps _ _ _ Hadj) as [Hlused _].
    specialize (Hlower l Hlused).
    assert (Hl : 0 <= l - 97 < 26) by lia.
    assert (Hedge : Znth x prev (-1) = l - 97).
    { apply (proj2 (Hpreviff (l - 97) x Hl Hx)).
      replace (97 + (l - 97)) with l by lia. exact Hadj. }
    lia. }
  split.
  - destruct Hcompat as [Hnodup [Hout Hin]]. repeat split.
    + intros word Hword. apply in_app_or in Hword. destruct Hword as [Hword | Hword].
      * apply Hnodup. apply in_or_app. left. exact Hword.
      * simpl in Hword. destruct Hword as [Heq | []]. subst word.
        apply NoDup_app. repeat split.
        -- apply Hnodup. apply in_or_app. right. simpl. auto.
        -- constructor. { simpl; auto. } constructor.
        -- intros c Hc Hsingle. change (97 + x = c \/ False) in Hsingle.
           destruct Hsingle as [Heq | []]. subst c. contradiction.
    + intros l r1 r2 H1 H2.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix (97 + x) (97 + last) l r1 Hprefix Htail)) in H1.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix (97 + x) (97 + last) l r2 Hprefix Htail)) in H2.
      destruct H1 as [H1 | [Hl1 Hr1]]; destruct H2 as [H2 | [Hl2 Hr2]].
      * eapply Hout; eauto.
      * subst l r2. exfalso. eapply Hnoout; eauto.
      * subst l r1. exfalso. eapply Hnoout; eauto.
      * congruence.
    + intros l1 l2 r H1 H2.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix (97 + x) (97 + last) l1 r Hprefix Htail)) in H1.
      apply (proj1 (adjacent_in_words_extend__word_scan_steps
        base prefix (97 + x) (97 + last) l2 r Hprefix Htail)) in H2.
      destruct H1 as [H1 | [Hl1 Hr1]]; destruct H2 as [H2 | [Hl2 Hr2]].
      * eapply Hin; eauto.
      * subst l2 r. exfalso. eapply Hnoin; eauto.
      * subst l1 r. exfalso. eapply Hnoin; eauto.
      * congruence.
  - destruct Hnext as [Hnextlen Hnextbounds].
    destruct Hprev as [Hprevlen Hprevbounds].
    destruct Hused as [Husedlen Husedbounds].
    split.
    + split. { rewrite replace_Znth_Zlength__word_scan_steps. exact Hnextlen. }
      intros k Hk. destruct (Z.eq_dec k last) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia. apply Hnextbounds. exact Hk.
    + split.
      * split. { rewrite replace_Znth_Zlength__word_scan_steps. exact Hprevlen. }
        intros k Hk. destruct (Z.eq_dec k x) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by lia. lia.
        -- rewrite Znth_replace_Znth_Diff by lia. apply Hprevbounds. exact Hk.
      * split.
        -- apply boolean_array_replace_one__word_scan_steps; [split; assumption|assumption].
        -- split.
           ++ intros c Hc. destruct (Z.eq_dec c x) as [-> | Hneq].
              ** rewrite Znth_replace_Znth_Same by lia. split; intro; [|reflexivity].
                 apply (proj2 (used_in_words_extend__word_scan_steps
                   base prefix (97 + x) (97 + x))). right. reflexivity.
              ** rewrite Znth_replace_Znth_Diff by lia. split; intro Hval.
                 --- apply (proj2 (used_in_words_extend__word_scan_steps
                       base prefix (97 + x) (97 + c))).
                     left. apply (proj1 (Husediff c Hc)). exact Hval.
                 --- apply (proj2 (Husediff c Hc)).
                     apply (proj1 (used_in_words_extend__word_scan_steps
                       base prefix (97 + x) (97 + c))) in Hval.
                     destruct Hval as [Hold | Heq]; [exact Hold|].
                     exfalso. apply Hneq. apply (Z.add_reg_l 97). exact Heq.
           ++ split.
              ** intros l r Hl Hr. destruct (Z.eq_dec l last) as [-> | Hneq].
                 --- rewrite Znth_replace_Znth_Same by lia. split; intro Hval.
                     +++ subst r. apply (proj2 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + last) (97 + x) Hprefix Htail)). right. auto.
                     +++ apply (proj1 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + last) (97 + r) Hprefix Htail)) in Hval.
                         destruct Hval as [Hold | [Heql Heqr]].
                         { exfalso. eapply Hnoout; eauto. }
                         symmetry. apply (Z.add_reg_l 97). exact Heqr.
                 --- rewrite Znth_replace_Znth_Diff by lia. split; intro Hval.
                     +++ apply (proj2 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + l) (97 + r) Hprefix Htail)). left.
                         apply (proj1 (Hnextiff l r Hl Hr)). exact Hval.
                     +++ apply (proj2 (Hnextiff l r Hl Hr)).
                         apply (proj1 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + l) (97 + r) Hprefix Htail)) in Hval.
                         destruct Hval as [Hold | [Heql Heqr]]; [exact Hold|].
                         exfalso. apply Hneq. apply (Z.add_reg_l 97). exact Heql.
              ** intros l r Hl Hr. destruct (Z.eq_dec r x) as [-> | Hneq].
                 --- rewrite Znth_replace_Znth_Same by lia. split; intro Hval.
                     +++ subst l. apply (proj2 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + last) (97 + x) Hprefix Htail)). right. auto.
                     +++ apply (proj1 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + l) (97 + x) Hprefix Htail)) in Hval.
                         destruct Hval as [Hold | [Heql Heqr]].
                         { exfalso. eapply Hnoin; eauto. }
                         symmetry. apply (Z.add_reg_l 97). exact Heql.
                 --- rewrite Znth_replace_Znth_Diff by lia. split; intro Hval.
                     +++ apply (proj2 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + l) (97 + r) Hprefix Htail)). left.
                         apply (proj1 (Hpreviff l r Hl Hr)). exact Hval.
                     +++ apply (proj2 (Hpreviff l r Hl Hr)).
                         apply (proj1 (adjacent_in_words_extend__word_scan_steps
                           base prefix (97 + x) (97 + last)
                           (97 + l) (97 + r) Hprefix Htail)) in Hval.
                         destruct Hval as [Hold | [Heql Heqr]]; [exact Hold|].
                         exfalso. apply Hneq. apply (Z.add_reg_l 97). exact Heqr.
Qed.
Lemma in_sublist_in__word_scan_steps :
  forall {A : Type} (x : A) lo hi (l : list A),
    In x (sublist lo hi l) -> In x l.
Proof.
  intros A x lo hi l Hin. unfold sublist in Hin.
  assert (Hfirst : In x (firstn (Z.to_nat hi) l)).
  { rewrite <- (firstn_skipn (Z.to_nat lo) (firstn (Z.to_nat hi) l)).
    apply in_or_app. right. exact Hin. }
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  apply in_or_app. left. exact Hfirst.
Qed.
Lemma word_scan_step_new_edge__word_scan_steps :
  forall given z i next prev used seen last x,
    0 <= z < Zlength given ->
    0 <= i < Zlength (Znth z given []) ->
    0 <= last < 26 -> 0 <= x < 26 ->
    WordScanState given z i next prev used seen last ->
    Znth i (Znth z given []) 0 = 97 + x ->
    Znth last next (-1) = -1 ->
    Znth x prev (-1) = -1 ->
    Znth x seen 0 = 0 ->
    WordScanState given z (i + 1)
      (replace_Znth last x next) (replace_Znth x last prev)
      (replace_Znth x 1 used) (replace_Znth x 1 seen) x.
Proof.
  intros given z i next prev used seen last x Hz Hi Hlast Hx Hstate Hchar
    Hnext Hprev Hseen.
  unfold WordScanState in Hstate |- *. fold (Znth z given []) in *.
  destruct Hstate as [Hpre [Henc [Hseenbool [Hseeniff Hlaststate]]]].
  destruct Hseenbool as [Hseenlen Hseenvals].
  set (word := Znth z given []) in *.
  set (base := sublist 0 z given) in *.
  set (prefix := sublist 0 i word) in *.
  assert (Hprefixlen : Zlength prefix = i).
  { unfold prefix. rewrite Zlength_sublist by lia. lia. }
  assert (Hprefixpos : 0 < Zlength prefix).
  { destruct Hlaststate as [[Hzero Hminus] | [Hpos Hlastold]]; [lia|].
    rewrite Hprefixlen. lia. }
  assert (Htail : Znth (Zlength prefix - 1) prefix 0 = 97 + last).
  { destruct Hlaststate as [[Hzero Hminus] | [Hpos Hlastold]]; [lia|].
    rewrite Hprefixlen. unfold prefix.
    rewrite (@Znth_sublist0 Z 0 (i - 1) i word) by lia. lia. }
  assert (Hfresh : ~ In (97 + x) prefix).
  { intro Hin. apply (proj2 (Hseeniff x Hx)) in Hin. congruence. }
  assert (Hlower : forall c, UsedInWords (base ++ [prefix]) c -> 97 <= c <= 122).
  { intros c (w & Hw & Hc). apply in_app_or in Hw. destruct Hw as [Hw | Hw].
    - unfold base in Hw. apply in_sublist_in__word_scan_steps in Hw.
      unfold Pre in Hpre. destruct Hpre as [Hlen Hwords].
      apply Forall_forall with (x := w) in Hwords; [|exact Hw].
      destruct Hwords as [_ Hletters]. unfold LowercaseLetter.
      apply Forall_forall with (x := c) in Hletters; assumption.
    - simpl in Hw. destruct Hw as [Heq | []]. subst w.
      unfold prefix in Hc. apply in_sublist_in__word_scan_steps in Hc.
      unfold Pre in Hpre. destruct Hpre as [Hlen Hwords].
      assert (Hwordin : In word given).
      { unfold word, Znth. apply nth_In. rewrite Zlength_correct in Hz. lia. }
      apply Forall_forall with (x := word) in Hwords; [|exact Hwordin].
      destruct Hwords as [_ Hletters]. unfold LowercaseLetter.
      apply Forall_forall with (x := c) in Hletters; assumption. }
  assert (Hencnew : EncodesGraph (base ++ [prefix ++ [97 + x]])
      (replace_Znth last x next) (replace_Znth x last prev)
      (replace_Znth x 1 used)).
  { eapply encodes_graph_extend_new__word_scan_steps; eauto. }
  split; [exact Hpre|]. split.
  - assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
    { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
      rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
    rewrite Hprefixeq. exact Hencnew.
  - split.
    + apply boolean_array_replace_one__word_scan_steps; [split; assumption|assumption].
    + split.
      * intros c Hc. destruct (Z.eq_dec c x) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by lia. split; intro; [|reflexivity].
           assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
           { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
             rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
           rewrite Hprefixeq. apply in_or_app. right. simpl. auto.
        -- rewrite Znth_replace_Znth_Diff by lia. rewrite Hseeniff by exact Hc.
           assert (Hprefixeq : sublist 0 (i + 1) word = prefix ++ [97 + x]).
           { unfold prefix. rewrite (sublist_split 0 (i + 1) i word) by lia.
             rewrite (@sublist_single Z 0 i word) by lia. rewrite Hchar. reflexivity. }
           rewrite Hprefixeq. split.
           ++ intro Hin. apply in_or_app. left. exact Hin.
           ++ intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact Hin|].
              change (97 + x = 97 + c \/ False) in Hin.
              destruct Hin as [Heq | []]. exfalso. apply Hneq.
              symmetry. apply (Z.add_reg_l 97). exact Heq.
      * right. split; [lia|]. replace (i + 1 - 1) with i by lia.
        rewrite Hchar. lia.
Qed.
Lemma word_scan_finish_graph_build__graph_build_boundary :
  forall given z scanned next prev used seen last,
    0 <= z < Zlength given ->
    0 <= scanned <= Zlength (Znth z given []) ->
    WordScanState given z scanned next prev used seen last ->
    Znth scanned (Znth z given [] ++ [0]) 0 = 0 ->
    GraphBuildState given (z + 1) next prev used.
Proof.
  intros given z scanned next prev used seen last
    Hz Hscanned Hscan Hzero.
  unfold WordScanState in Hscan.
  destruct Hscan as [Hpre [Hgraph Hrest]].
  assert (Hscanlen : scanned = Zlength (Znth z given [])).
  {
    destruct (Z_lt_ge_dec scanned (Zlength (Znth z given []))) as
      [Hinside | Hatend]; [| lia].
    unfold Pre in Hpre.
    destruct Hpre as [_ Hwords].
    pose proof
      ((proj1 (Forall_Znth
        (fun word =>
          0 < Zlength word <= 100000 /\ Forall LowercaseLetter word)
        [] given)) Hwords z Hz) as Hzword.
    destruct Hzword as [_ Hchars].
    pose proof
      ((proj1 (Forall_Znth LowercaseLetter 0 (Znth z given [])))
        Hchars scanned ltac:(lia)) as Hchar.
    unfold LowercaseLetter in Hchar.
    rewrite app_Znth1 in Hzero by lia.
    lia.
  }
  subst scanned.
  unfold GraphBuildState.
  split; [exact Hpre |].
  rewrite
    (sublist_self (Znth z given []) (Zlength (Znth z given [])) eq_refl)
    in Hgraph.
  rewrite (sublist_split 0 (z + 1) z given) by lia.
  rewrite (sublist_single [] z given) by lia.
  exact Hgraph.
Qed.
Lemma traversal_state_zero__traversal_initialization :
  forall next prev used visited,
    BooleanArray visited -> AllZero visited ->
    TraversalState next prev used 0 visited [].
Proof.
  intros next prev used visited Hboolean Hzero.
  unfold TraversalState.
  split.
  - unfold CompletedHeadSet.
    split.
    + exact Hboolean.
    + intros c Hc.
      split.
      * intro Hone.
        unfold AllZero in Hzero.
        rewrite Hzero in Hone.
        2: { destruct Hboolean as [Hlength _]. lia. }
        discriminate.
      * intros (head & Hhead & _).
        lia.
  - split.
    + unfold OutputMatchesVisited.
      split.
      * constructor.
      * intros c Hc.
        split.
        -- intro Hone.
           unfold AllZero in Hzero.
           rewrite Hzero in Hone.
           2: { destruct Hboolean as [Hlength _]. lia. }
           discriminate.
        -- intro Hin.
           contradiction.
    + apply ordered_traversal_zero.
Qed.
Lemma encoded_next_prev__traversal_initialization :
  forall words next prev used from to,
    EncodesGraph words next prev used ->
    0 <= from < 26 -> 0 <= to < 26 ->
    Znth from next (-1) = to ->
    Znth to prev (-1) = from.
Proof.
  intros words next prev used from to Henc Hfrom Hto Hedge.
  unfold EncodesGraph in Henc.
  destruct Henc as (_ & _ & _ & _ & _ & Hnext & Hprev).
  apply (proj2 (Hprev from to Hfrom Hto)).
  apply (proj1 (Hnext from to Hfrom Hto)).
  exact Hedge.
Qed.
Lemma next_reach_last__traversal_initialization :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    start = target \/
    exists pred,
      NextReach next start pred /\ 0 <= pred < 26 /\
      0 <= target < 26 /\ Znth pred next (-1) = target.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach as [x|from mid to Hedge Hmid Hreach IH].
  - left. reflexivity.
  - destruct (IH Hmid) as [Heq | (pred & Hrp & Hpred & Hto & Hlast)].
    + subst to. right. exists from.
      split. constructor. split. exact Hstart. split; assumption.
    + right. exists pred.
      split. eapply next_reach_step; eauto.
      split. exact Hpred. split; assumption.
Qed.
Lemma path_scan_start__traversal_initialization :
  forall words words_done next prev used start visited output,
    GraphBuildState words words_done next prev used ->
    TraversalState next prev used start visited output ->
    0 <= start < 26 ->
    Znth start used 0 <> 0 ->
    Znth start prev 0 < 0 ->
    PathScanState next prev used start start visited output.
Proof.
  intros words words_done next prev used start visited output
    Hbuild Htraversal Hstart Husednz Hprevneg.
  destruct Hbuild as [Hpre Henc].
  pose proof Henc as Henc0.
  unfold EncodesGraph in Henc.
  destruct Henc as
    [Hcompatible [Hnext [Hprev [Hused [HusedWords
      [HnextEdges HprevEdges]]]]]].
  destruct Hused as [Husedlen Husedvalues].
  destruct Hprev as [Hprevlen Hprevvalues].
  assert (Husedone : Znth start used 0 = 1).
  {
    destruct (Husedvalues start Hstart) as [Hzero | Hone].
    - contradiction.
    - exact Hone.
  }
  assert (Hprevdefault : Znth start prev (-1) = Znth start prev 0).
  {
    apply Znth_indep.
    lia.
  }
  assert (Hprevminus : Znth start prev (-1) = -1).
  {
    destruct (Hprevvalues start Hstart) as [Hlower Hupper].
    rewrite Hprevdefault in Hlower, Hupper.
    rewrite Hprevdefault.
    lia.
  }
  assert (Hhead : IsHead prev used start).
  {
    unfold IsHead.
    split; [exact Hstart|].
    split; assumption.
  }
  pose proof Htraversal as Htraversal0.
  unfold TraversalState in Htraversal.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  unfold CompletedHeadSet in Hcompleted.
  destruct Hcompleted as [Hvisitedbool Hcompleted].
  destruct Hvisitedbool as [Hvisitedlen Hvisitedvalues].
  assert (Hunvisited : Znth start visited 0 = 0).
  {
    destruct (Hvisitedvalues start Hstart) as [Hzero | Hone].
    - exact Hzero.
    - exfalso.
      apply (proj1 (Hcompleted start Hstart)) in Hone.
      destruct Hone as (old_head & Hold & Holdhead & Hreach).
      destruct Holdhead as [Holdbounds [Holduse Holdprev]].
      destruct (next_reach_last__traversal_initialization
        next old_head start Holdbounds Hreach) as
        [Heq | (pred & Hpredreach & Hpredbounds & Hstartbounds & Hedge)].
      + lia.
      + pose proof (encoded_next_prev__traversal_initialization
          (sublist 0 words_done words) next prev used pred start
          Henc0 Hpredbounds Hstartbounds Hedge)
          as Hbad.
        rewrite Hprevminus in Hbad.
        lia.
  }
  unfold PathScanState.
  exists visited, output, (@nil Z).
  refine (conj Htraversal0 (conj Hhead (conj _ (conj _ (conj _ _))))).
  - apply path_prefix_start.
  - unfold MarkedPath.
    split.
    + split; assumption.
    + split.
      * split; assumption.
      * intros c Hc. simpl. tauto.
  - simpl. rewrite app_nil_r. reflexivity.
  - right. split; assumption.
Qed.
Lemma encoded_next_prev__path_entry_step :
  forall words next prev used from to,
    EncodesGraph words next prev used ->
    0 <= from < 26 -> 0 <= to < 26 ->
    Znth from next (-1) = to ->
    Znth to prev (-1) = from.
Proof.
  intros words next prev used from to Henc Hfrom Hto Hedge.
  unfold EncodesGraph in Henc.
  destruct Henc as (_ & _ & _ & _ & _ & Hnext & Hprev).
  apply (proj2 (Hprev from to Hfrom Hto)).
  apply (proj1 (Hnext from to Hfrom Hto)).
  exact Hedge.
Qed.
Lemma next_reach_target_valid__path_entry_step :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    0 <= target < 26.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach.
  - exact Hstart.
  - apply IHHreach. exact H0.
Qed.
Lemma next_reach_last__path_entry_step :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    start = target \/
    exists pred,
      NextReach next start pred /\ 0 <= pred < 26 /\
      0 <= target < 26 /\ Znth pred next (-1) = target.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach as [x|from mid to Hedge Hmid Hreach IH].
  - left. reflexivity.
  - destruct (IH Hmid) as [Heq | (pred & Hrp & Hpred & Hto & Hlast)].
    + subst to. right. exists from.
      split. constructor. split. exact Hstart. split; assumption.
    + right. exists pred.
      split. eapply next_reach_step; eauto.
      split. exact Hpred. split; assumption.
Qed.
Lemma path_prefix_member_bounds__path_entry_step :
  forall next start path current x,
    PathPrefix next start path current -> In x path ->
    0 <= x < 26.
Proof.
  intros next start path current x Hpath.
  induction Hpath as [|p c succ Hp IH Hc Hedge]; intro Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [<- | []]. exact Hc.
Qed.
Lemma path_prefix_member_prefix__path_entry_step :
  forall next start path current x,
    PathPrefix next start path current -> In x path ->
    exists before after,
      path = before ++ x :: after /\
      PathPrefix next start before x.
Proof.
  intros next start path current x Hpath.
  induction Hpath as [|p c succ Hp IH Hc Hedge]; intro Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (IH Hin) as (before & after & Heq & Hpre).
      exists before, (after ++ (c :: @nil Z)).
      split. rewrite Heq. rewrite <- app_assoc. reflexivity. exact Hpre.
    + simpl in Hin. destruct Hin as [<- | []].
      exists p, (@nil Z). split. reflexivity. exact Hp.
Qed.
Lemma head_reaching_path_current_unique__path_entry_step :
  forall words next prev used start path current head,
    EncodesGraph words next prev used ->
    IsHead prev used start -> IsHead prev used head ->
    PathPrefix next start path current ->
    NextReach next head current -> head = start.
Proof.
  intros words next prev used start path current head
    Henc Hstart Hhead Hpath.
  destruct Hstart as [Hstartb [Hstartu Hstartp]].
  induction Hpath as [|p cur succ Hp IH Hcur Hedge]; intro Hreach.
  - destruct Hhead as [Hheadb [Hheadu Hheadp]].
    destruct (next_reach_last__path_entry_step
      next head start Hheadb Hreach) as [Heq | (pred & Hrp & Hpred & Hsb & Hlast)].
    + exact Heq.
    + pose proof (encoded_next_prev__path_entry_step
        words next prev used pred start Henc Hpred Hsb Hlast) as Hprev.
      rewrite Hstartp in Hprev. lia.
  - destruct Hhead as [Hheadb [Hheadu Hheadp]].
    pose proof (next_reach_target_valid__path_entry_step
      next head succ Hheadb Hreach) as Hsucc.
    destruct (next_reach_last__path_entry_step
      next head succ Hheadb Hreach) as [Heq | (pred & Hrp & Hpred & _ & Hlast)].
    + subst head.
      pose proof (encoded_next_prev__path_entry_step
        words next prev used cur succ Henc Hcur Hsucc Hedge) as Hprev.
      rewrite Hheadp in Hprev. lia.
    + pose proof (encoded_next_prev__path_entry_step
        words next prev used cur succ Henc Hcur Hsucc Hedge) as Hprev1.
      pose proof (encoded_next_prev__path_entry_step
        words next prev used pred succ Henc Hpred Hsucc Hlast) as Hprev2.
      assert (Heqpred : pred = cur) by congruence.
      rewrite Heqpred in Hrp.
      apply IH. exact Hrp.
Qed.
Lemma completed_path_nodup__path_entry_step :
  forall words next prev used start path current,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path current ->
    NoDup path /\ ~ In current path.
Proof.
  assert (Hnil : forall next0 start0 current0,
    PathPrefix next0 start0 (@nil Z) current0 -> current0 = start0).
  { intros next0 start0 current0 H0. remember (@nil Z) as p eqn:Heq.
    induction H0; subst; auto.
    apply app_eq_nil in Heq. destruct Heq as [_ Hbad]. discriminate. }
  intros words next prev used start path current Henc Hhead Hpath.
  destruct Hhead as [Hstartb [Hstartu Hstartprev]].
  induction Hpath as [|p cur succ Hp IH Hcur Hedge].
  - split. constructor. intro H. exact H.
  - destruct IH as [Hnd Hfresh].
    assert (Hndfull : NoDup (p ++ cur :: @nil Z)).
    { apply NoDup_app. repeat split.
      - exact Hnd.
      - constructor. intro H. exact H. constructor.
      - intros x Hinx Hinone. simpl in Hinone.
        destruct Hinone as [-> | []]. contradiction. }
    split. exact Hndfull.
    intro Hinsucc.
    apply in_app_or in Hinsucc. destruct Hinsucc as [Hinold | Hinlast].
    + destruct (path_prefix_member_prefix__path_entry_step
        next start p cur succ Hp Hinold)
        as (before & after & Heqp & Hbefore).
      pose proof Hedge as Hedge_outer.
      destruct before as [|a before'].
      * assert (Heqsucc : succ = start) by
          (apply Hnil with (next0 := next); exact Hbefore).
        pose proof (encoded_next_prev__path_entry_step
          words next prev used cur start Henc Hcur Hstartb
          (eq_trans Hedge_outer Heqsucc)) as Hbad.
        rewrite Hstartprev in Hbad. lia.
      * inversion Hbefore as [|prefix pred target Hprefix Hpredbound Hedgepred Heqpath].
        pose proof (path_prefix_member_bounds__path_entry_step
          next start p cur succ Hp Hinold) as Hsucc.
        pose proof (encoded_next_prev__path_entry_step
          words next prev used cur succ Henc Hcur Hsucc Hedge_outer) as Hprev1.
        pose proof (encoded_next_prev__path_entry_step
          words next prev used pred succ Henc Hpredbound Hsucc Hedgepred) as Hprev2.
        assert (Heqpred : pred = cur) by congruence.
        apply Hfresh. rewrite Heqp.
        rewrite <- Heqpred. apply in_or_app. left. rewrite <- Heqpath.
        apply in_or_app. right. simpl. auto.
    + simpl in Hinlast. destruct Hinlast as [Heq | []].
      assert (Hedge_self : Znth cur next (-1) = cur) by congruence.
      destruct p as [|a p'].
      * assert (Heqcur : cur = start) by
          (apply Hnil with (next0 := next); exact Hp).
        pose proof (encoded_next_prev__path_entry_step
          words next prev used cur start Henc Hcur Hstartb
          (eq_trans Hedge_self Heqcur)) as Hbad.
        rewrite Hstartprev in Hbad. lia.
      * inversion Hp as [|prefix pred target Hprefix Hpredbound Hedgepred Heqpath].
        pose proof (encoded_next_prev__path_entry_step
          words next prev used pred cur Henc Hpredbound Hcur Hedgepred) as Hprev1.
        pose proof (encoded_next_prev__path_entry_step
          words next prev used cur cur Henc Hcur Hcur Hedge_self) as Hprev2.
        assert (Heqpred : pred = cur) by congruence.
        apply Hfresh. rewrite <- Heqpred. rewrite <- Heqpath.
        apply in_or_app. right. simpl. auto.
Qed.
Lemma length_replace_nth__path_entry_step :
  forall {A : Type} (values : list A) n value,
    length (replace_nth n values value) = length values.
Proof.
  intros A values.
  induction values as [|x values IH]; intros n value; simpl.
  - reflexivity.
  - destruct n; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma Zlength_replace_Znth__path_entry_step :
  forall {A : Type} (values : list A) c value,
    Zlength (replace_Znth c value values) = Zlength values.
Proof.
  intros A values c value.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite length_replace_nth__path_entry_step.
  reflexivity.
Qed.
Lemma boolean_array_replace_one__path_entry_step :
  forall values c,
    BooleanArray values -> 0 <= c < 26 ->
    BooleanArray (replace_Znth c 1 values).
Proof.
  intros values c [Hlen Hvalues] Hc.
  unfold BooleanArray.
  split.
  - rewrite Zlength_replace_Znth__path_entry_step. exact Hlen.
  - intros k Hk. destruct (Z.eq_dec k c) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia. right. reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hvalues. exact Hk.
Qed.
Lemma marked_path_extend__path_entry_step :
  forall before path after c,
    MarkedPath before path after -> 0 <= c < 26 ->
    MarkedPath before (path ++ [c]) (replace_Znth c 1 after).
Proof.
  intros before path after c Hmarked Hc.
  unfold MarkedPath in *.
  destruct Hmarked as [Hbefore [Hafter Hmarked]].
  destruct Hafter as [Hafterlen Haftervalues].
  refine (conj Hbefore (conj
    (boolean_array_replace_one__path_entry_step after c
      (conj Hafterlen Haftervalues) Hc) _)).
  intros k Hk. destruct (Z.eq_dec k c) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    split; intro H; [right | reflexivity].
    apply in_or_app. right. simpl. auto.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Hmarked by exact Hk.
    split.
    + intros [Hbeforeone | Hin].
      * left. exact Hbeforeone.
      * right. apply in_or_app. left. exact Hin.
    + intros [Hbeforeone | Hin].
      * left. exact Hbeforeone.
      * right. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        -- exact Hin.
        -- simpl in Hin. destruct Hin as [Heq | []].
           exfalso. apply Hneq. symmetry. exact Heq.
Qed.
Lemma partial_path_current_not_completed__path_entry_step :
  forall words next prev used start path current visited_before output_before,
    EncodesGraph words next prev used ->
    TraversalState next prev used start visited_before output_before ->
    IsHead prev used start ->
    PathPrefix next start path current ->
    0 <= current < 26 ->
    Znth current visited_before 0 = 0.
Proof.
  intros words next prev used start path current visited_before output_before
    Henc Htraversal Hhead Hpath Hcurrent.
  unfold TraversalState in Htraversal.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  unfold CompletedHeadSet in Hcompleted.
  destruct Hcompleted as [Hbool Hcompleted].
  destruct Hbool as [Hlen Hbool].
  destruct (Hbool current Hcurrent) as [Hzero | Hone]; [exact Hzero|].
  exfalso.
  apply (proj1 (Hcompleted current Hcurrent)) in Hone.
  destruct Hone as (old_head & Hold & Holdhead & Hreach).
  pose proof (head_reaching_path_current_unique__path_entry_step
    words next prev used start path current old_head
    Henc Hhead Holdhead Hpath Hreach) as Heq.
  lia.
Qed.
Lemma path_scan_state_extend__path_entry_step :
  forall words next prev used start current visited output,
    EncodesGraph words next prev used ->
    PathScanState next prev used start current visited output ->
    0 <= current < 26 ->
    Znth current visited 0 = 0 ->
    PathScanState next prev used start (Znth current next 0)
      (replace_Znth current 1 visited) (output ++ [97 + current]).
Proof.
  intros words next prev used start current visited output
    Henc Hscan Hcurrent Hcurrentzero.
  unfold PathScanState in Hscan.
  destruct Hscan as (visited_before & output_before & path &
    Htraversal & Hhead & Hpath & Hmarked & Houtput & Hexit).
  pose proof Henc as Henc0.
  unfold EncodesGraph in Henc.
  destruct Henc as
    [Hcompatible [Hnextbounds [Hprevbounds [Hused [HusedWords
      [HnextEdges HprevEdges]]]]]].
  destruct Hnextbounds as [Hnextlen Hnextbounds].
  assert (Hedge : Znth current next (-1) = Znth current next 0).
  { apply Znth_indep. lia. }
  assert (Hpath' : PathPrefix next start (path ++ [current])
      (Znth current next 0)).
  { eapply path_prefix_step; eauto. }
  assert (Hmarked' : MarkedPath visited_before (path ++ [current])
      (replace_Znth current 1 visited)).
  { apply marked_path_extend__path_entry_step; assumption. }
  assert (Hexit' : Znth current next 0 = -1 \/
      (0 <= Znth current next 0 < 26 /\
       Znth (Znth current next 0) (replace_Znth current 1 visited) 0 = 0)).
  {
    destruct (Hnextbounds current Hcurrent) as [Hlower Hupper].
    rewrite Hedge in Hlower, Hupper.
    destruct (Z.eq_dec (Znth current next 0) (-1)) as [Heq | Hneq].
    - left. exact Heq.
    - right. split; [lia|].
      assert (Hsuccessor : 0 <= Znth current next 0 < 26) by lia.
      pose proof (partial_path_current_not_completed__path_entry_step
        words next prev used start (path ++ [current]) (Znth current next 0)
        visited_before output_before
        Henc0
        Htraversal Hhead Hpath' Hsuccessor) as Hbeforezero.
      destruct (completed_path_nodup__path_entry_step
        words next prev used start (path ++ [current]) (Znth current next 0)
        Henc0
        Hhead Hpath') as [Hnodup Hnotin].
      unfold MarkedPath in Hmarked'.
      destruct Hmarked' as [Hbeforebool [Hafterbool Hmarked']].
      destruct Hafterbool as [Hafterlen Haftervalues].
      destruct (Haftervalues (Znth current next 0) Hsuccessor) as
        [Hzero | Hone]; [exact Hzero|].
      exfalso.
      apply (proj1 (Hmarked' (Znth current next 0) Hsuccessor)) in Hone.
      destruct Hone as [Hbad | Hbad].
      + rewrite Hbeforezero in Hbad. discriminate.
      + contradiction.
  }
  unfold PathScanState.
  exists visited_before, output_before, (path ++ [current]).
  refine (conj Htraversal (conj Hhead (conj Hpath' (conj Hmarked' (conj _ Hexit'))))).
  rewrite Houtput.
  rewrite map_app. simpl.
  rewrite app_assoc. reflexivity.
Qed.
Lemma path_scan_step__path_extension :
  forall words next prev used start current visited output,
    EncodesGraph words next prev used ->
    PathScanState next prev used start current visited output ->
    0 <= current < 26 ->
    Znth current visited 0 = 0 ->
    PathScanState next prev used start (Znth current next 0)
      (replace_Znth current 1 visited) (output ++ [97 + current]).
Proof.
  intros.
  eapply path_scan_state_extend__path_entry_step; eauto.
Qed.
Lemma mapped_path_nodup__path_extension :
  forall (path : list Z),
    NoDup path -> NoDup (map (fun c => 97 + c) path).
Proof.
  intros path Hnd. induction Hnd.
  - constructor.
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as (y & Heq & Hiny).
      change (97 + y = 97 + x) in Heq.
      apply Z.add_reg_l in Heq. subst y. contradiction.
    + exact IHHnd.
Qed.
Lemma partial_path_disjoint_output__path_extension :
  forall words next prev used start path current visited_before output_before,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path current ->
    CompletedHeadSet next prev used start visited_before ->
    OutputMatchesVisited visited_before output_before ->
    forall x, In x path -> ~ In (97 + x) output_before.
Proof.
  intros words next prev used start path current visited_before output_before
    Henc Hhead Hpath Hcompleted Houtput x Hinx Hinout.
  unfold CompletedHeadSet in Hcompleted.
  destruct Hcompleted as [Hbool Hcompleted].
  unfold OutputMatchesVisited in Houtput.
  destruct Houtput as [Hndout Houtput].
  pose proof (path_prefix_member_bounds__path_entry_step
    next start path current x Hpath Hinx) as Hx.
  apply (proj2 (Houtput x Hx)) in Hinout.
  apply (proj1 (Hcompleted x Hx)) in Hinout.
  destruct Hinout as (old_head & Holdlt & Holdhead & Holdreach).
  destruct (path_prefix_member_prefix__path_entry_step
    next start path current x Hpath Hinx)
    as (before & after & Heq & Hbefore).
  pose proof (head_reaching_path_current_unique__path_entry_step
    words next prev used start before x old_head Henc Hhead Holdhead
    Hbefore Holdreach) as Heqhead.
  lia.
Qed.
Lemma output_matches_visited_add_prefix__path_extension :
  forall words next prev used start path current visited_before visited_after output_before,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path current ->
    CompletedHeadSet next prev used start visited_before ->
    OutputMatchesVisited visited_before output_before ->
    MarkedPath visited_before path visited_after ->
    OutputMatchesVisited visited_after
      (output_before ++ map (fun c => 97 + c) path).
Proof.
  intros words next prev used start path current visited_before visited_after output_before
    Henc Hhead Hpath Hcompleted Houtput Hmarked.
  unfold OutputMatchesVisited in *.
  destruct Houtput as [Hndout Houtput].
  unfold MarkedPath in Hmarked.
  destruct Hmarked as [Hbeforebool [Hafterbool Hmarked]].
  split.
  - apply NoDup_app. repeat split.
    + exact Hndout.
    + apply mapped_path_nodup__path_extension.
      apply (proj1 (completed_path_nodup__path_entry_step
        words next prev used start path current Henc Hhead Hpath)).
    + intros y Hinyout Hinymap.
      apply in_map_iff in Hinymap.
      destruct Hinymap as (x & Heq & Hinx).
      change (97 + x = y) in Heq.
      subst y.
      apply (partial_path_disjoint_output__path_extension
        words next prev used start path current visited_before output_before
        Henc Hhead Hpath Hcompleted (conj Hndout Houtput) x Hinx).
      exact Hinyout.
  - intros c Hc. rewrite Hmarked by exact Hc.
    rewrite in_app_iff. rewrite <- Houtput by exact Hc.
    split.
    + intros [Hbefore | Hinpath]. left. exact Hbefore.
      right. apply in_map. exact Hinpath.
    + intros [Hbefore | Hinmap]. left. exact Hbefore.
      right. apply in_map_iff in Hinmap.
      destruct Hinmap as (x & Heq & Hinx).
      change (97 + x = 97 + c) in Heq.
      apply Z.add_reg_l in Heq. subst x. exact Hinx.
Qed.
Lemma path_scan_output_matches__path_extension :
  forall words next prev used start current visited output,
    EncodesGraph words next prev used ->
    PathScanState next prev used start current visited output ->
    OutputMatchesVisited visited output.
Proof.
  intros words next prev used start current visited output Henc Hscan.
  unfold PathScanState in Hscan.
  destruct Hscan as (visited_before & output_before & path &
    Htraversal & Hhead & Hpath & Hmarked & Houtput & Hexit).
  unfold TraversalState in Htraversal.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  subst output.
  eapply output_matches_visited_add_prefix__path_extension; eauto.
Qed.
Lemma ordered_traversal_output_bounds__path_extension :
  forall next prev used bound output,
    OrderedTraversal next prev used bound output ->
    Forall (fun x => 97 <= x < 123) output.
Proof.
  intros next prev used bound output Hordered.
  induction Hordered.
  - constructor.
  - exact IHHordered.
  - apply Forall_app. split.
    + exact IHHordered.
    + apply Forall_forall. intros x Hinx.
      apply in_map_iff in Hinx.
      destruct Hinx as (c & <- & Hinc).
      pose proof (path_prefix_member_bounds__path_entry_step
        next bound path (-1) c H1 Hinc).
      lia.
Qed.
Lemma path_scan_output_bounds__path_extension :
  forall next prev used start current visited output,
    PathScanState next prev used start current visited output ->
    Forall (fun x => 97 <= x < 123) output.
Proof.
  intros next prev used start current visited output Hscan.
  unfold PathScanState in Hscan.
  destruct Hscan as (visited_before & output_before & path &
    Htraversal & Hhead & Hpath & Hmarked & Houtput & Hexit).
  unfold TraversalState in Htraversal.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  subst output.
  apply Forall_app. split.
  - eapply ordered_traversal_output_bounds__path_extension; eauto.
  - apply Forall_forall. intros x Hinx.
    apply in_map_iff in Hinx.
    destruct Hinx as (c & <- & Hinc).
    pose proof (path_prefix_member_bounds__path_entry_step
      next start path current c Hpath Hinc).
    lia.
Qed.
Lemma bounded_letter_in_alphabet__path_extension :
  forall x,
    97 <= x < 123 ->
    In x (map (fun n : nat => 97 + Z.of_nat n) (List.seq 0%nat 26%nat)).
Proof.
  intros x Hx.
  apply in_map_iff.
  exists (Z.to_nat (x - 97)).
  split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. simpl.
    assert (Hlt : (Z.to_nat (x - 97) < Z.to_nat 26)%nat).
    { apply Z2Nat.inj_lt; lia. }
    simpl in Hlt. lia.
Qed.
Lemma output_matches_visited_length_bound__path_extension :
  forall words next prev used start current visited output,
    EncodesGraph words next prev used ->
    PathScanState next prev used start current visited output ->
    0 <= current < 26 ->
    Znth current visited 0 = 0 ->
    Zlength (output ++ [97 + current]) <= 26.
Proof.
  intros words next prev used start current visited output
    Henc Hscan Hcurrent Hunvisited.
  pose proof (path_scan_output_matches__path_extension
    words next prev used start current visited output Henc Hscan) as Hmatches.
  pose proof (path_scan_output_bounds__path_extension
    next prev used start current visited output Hscan) as Hbounds.
  destruct Hmatches as [Hnodup Hmatches].
  assert (Hnotin : ~ In (97 + current) output).
  { intro Hin.
    apply (proj2 (Hmatches current Hcurrent)) in Hin.
    lia. }
  assert (Hnodup' : NoDup (output ++ [97 + current])).
  { apply NoDup_app. repeat split.
    - exact Hnodup.
    - constructor. simpl. tauto. constructor.
    - intros x Hinx Hinone.
      simpl in Hinone. destruct Hinone as [<- | []]. contradiction. }
  assert (Hbounds' : Forall (fun x => 97 <= x < 123)
      (output ++ [97 + current])).
  { apply Forall_app. split.
    - exact Hbounds.
    - constructor; [lia | constructor]. }
  assert (Hincl : incl (output ++ [97 + current])
      (map (fun n : nat => 97 + Z.of_nat n) (List.seq 0%nat 26%nat))).
  { intros x Hinx.
    apply bounded_letter_in_alphabet__path_extension.
    rewrite Forall_forall in Hbounds'.
    apply Hbounds'. exact Hinx. }
  pose proof (NoDup_incl_length Hnodup' Hincl) as Hlen.
  rewrite Zlength_correct.
  rewrite length_map, length_seq in Hlen.
  lia.
Qed.
Lemma encoded_next_prev__path_exits_head_skip :
  forall words next prev used from to,
    EncodesGraph words next prev used ->
    0 <= from < 26 -> 0 <= to < 26 ->
    Znth from next (-1) = to ->
    Znth to prev (-1) = from.
Proof.
  intros words next prev used from to Henc Hfrom Hto Hedge.
  unfold EncodesGraph in Henc.
  destruct Henc as (_ & _ & _ & _ & _ & Hnext & Hprev).
  apply (proj2 (Hprev from to Hfrom Hto)).
  apply (proj1 (Hnext from to Hfrom Hto)).
  exact Hedge.
Qed.
Lemma next_reach_target_valid__path_exits_head_skip :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    0 <= target < 26.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach.
  - exact Hstart.
  - apply IHHreach. exact H0.
Qed.
Lemma next_reach_last__path_exits_head_skip :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    start = target \/
    exists pred,
      NextReach next start pred /\ 0 <= pred < 26 /\
      0 <= target < 26 /\ Znth pred next (-1) = target.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach as [x|from mid to Hedge Hmid Hreach IH].
  - left. reflexivity.
  - destruct (IH Hmid) as [Heq | (pred & Hrp & Hpred & Hto & Hlast)].
    + subst to. right. exists from.
      split. constructor. split. exact Hstart. split; assumption.
    + right. exists pred.
      split. eapply next_reach_step; eauto.
      split. exact Hpred. split; assumption.
Qed.
Lemma path_prefix_member_bounds__path_exits_head_skip :
  forall next start path current x,
    PathPrefix next start path current -> In x path ->
    0 <= x < 26.
Proof.
  intros next start path current x Hpath.
  induction Hpath as [|p c succ Hp IH Hc Hedge]; intro Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [<- | []]. exact Hc.
Qed.
Lemma path_prefix_member_reach__path_exits_head_skip :
  forall next start path current x,
    PathPrefix next start path current -> In x path ->
    NextReach next start x.
Proof.
  assert (Htrans : forall next a b c,
    NextReach next a b -> NextReach next b c -> NextReach next a c).
  { intros next0 a b c Hab Hbc. induction Hab.
    - exact Hbc.
    - eapply next_reach_step; eauto. }
  assert (Hcurrent : forall next start path current,
    PathPrefix next start path current -> 0 <= current < 26 ->
    NextReach next start current).
  { intros next0 start0 path0 current0 Hp0 Hcurrent0.
    induction Hp0 as [|p cur succ Hp IH Hcur Hedge].
    - constructor.
    - eapply Htrans. apply IH. exact Hcur.
      eapply next_reach_step. exact Hedge. exact Hcurrent0. constructor. }
  intros next start path current x Hpath.
  induction Hpath as [|p c succ Hp IH Hc Hedge]; intro Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [<- | []].
      apply Hcurrent with (path := p). exact Hp. exact Hc.
Qed.
Lemma head_reaching_path_current_unique__path_exits_head_skip :
  forall words next prev used start path current head,
    EncodesGraph words next prev used ->
    IsHead prev used start -> IsHead prev used head ->
    PathPrefix next start path current ->
    NextReach next head current -> head = start.
Proof.
  intros words next prev used start path current head
    Henc Hstart Hhead Hpath.
  destruct Hstart as [Hstartb [Hstartu Hstartp]].
  induction Hpath as [|p cur succ Hp IH Hcur Hedge]; intro Hreach.
  - destruct Hhead as [Hheadb [Hheadu Hheadp]].
    destruct (next_reach_last__path_exits_head_skip
      next head start Hheadb Hreach) as [Heq | (pred & Hrp & Hpred & Hsb & Hlast)].
    + exact Heq.
    + pose proof (encoded_next_prev__path_exits_head_skip
        words next prev used pred start Henc Hpred Hsb Hlast) as Hprev.
      rewrite Hstartp in Hprev. lia.
  - destruct Hhead as [Hheadb [Hheadu Hheadp]].
    pose proof (next_reach_target_valid__path_exits_head_skip
      next head succ Hheadb Hreach) as Hsucc.
    destruct (next_reach_last__path_exits_head_skip
      next head succ Hheadb Hreach) as [Heq | (pred & Hrp & Hpred & _ & Hlast)].
    + subst head.
      pose proof (encoded_next_prev__path_exits_head_skip
        words next prev used cur succ Henc Hcur Hsucc Hedge) as Hprev.
      rewrite Hheadp in Hprev. lia.
    + pose proof (encoded_next_prev__path_exits_head_skip
        words next prev used cur succ Henc Hcur Hsucc Hedge) as Hprev1.
      pose proof (encoded_next_prev__path_exits_head_skip
        words next prev used pred succ Henc Hpred Hsucc Hlast) as Hprev2.
      assert (Heqpred : pred = cur) by congruence.
      rewrite Heqpred in Hrp.
      apply IH. exact Hrp.
Qed.
Lemma path_prefix_first__path_exits_head_skip :
  forall next start path current,
    PathPrefix next start path current ->
    (path = (@nil Z) /\ current = start) \/
    exists rest successor,
      path = start :: rest /\
      Znth start next (-1) = successor /\
      PathPrefix next successor rest current.
Proof.
  intros next start path current Hpath.
  induction Hpath as [|p cur succ Hp IH Hcur Hedge].
  - left. auto.
  - destruct IH as [[-> ->] | (rest & first & Heq & Hfirst & Hsuffix)].
    + right. exists (@nil Z), succ. simpl. repeat split; try assumption.
      constructor.
    + right. exists (rest ++ (cur :: @nil Z)), first.
      split. rewrite Heq. reflexivity.
      split. exact Hfirst.
      eapply path_prefix_step; eauto.
Qed.
Lemma reachable_in_completed_path__path_exits_head_skip :
  forall next start target,
    0 <= start < 26 -> NextReach next start target ->
    forall path, PathPrefix next start path (-1) -> In target path.
Proof.
  intros next start target Hstart Hreach.
  induction Hreach as [s|from mid to Hedge Hmid Htail IH];
    intros path Hpath.
  - destruct (path_prefix_first__path_exits_head_skip
      next s path (-1) Hpath) as [[Hem Hbad] |
        (rest & succ & Heq & Hedge0 & Hsuffix)].
    + lia.
    + rewrite Heq. simpl. auto.
  - destruct (path_prefix_first__path_exits_head_skip
      next from path (-1) Hpath) as [[Hem Hbad] |
        (rest & succ & Heq & Hedge0 & Hsuffix)].
    + lia.
    + assert (Heqsucc : succ = mid) by congruence.
      rewrite Heqsucc in Hsuffix.
      rewrite Heq. simpl. right. apply IH. exact Hmid. exact Hsuffix.
Qed.
Lemma path_prefix_member_prefix__path_exits_head_skip :
  forall next start path current x,
    PathPrefix next start path current -> In x path ->
    exists before after,
      path = before ++ x :: after /\
      PathPrefix next start before x.
Proof.
  intros next start path current x Hpath.
  induction Hpath as [|p cur succ Hp IH Hcur Hedge]; intro Hin.
  - contradiction.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (IH Hin) as (before & after & Heq & Hpre).
      exists before, (after ++ (cur :: @nil Z)).
      split. rewrite Heq. rewrite <- app_assoc. reflexivity. exact Hpre.
    + simpl in Hin. destruct Hin as [<- | []].
      exists p, (@nil Z). split. reflexivity. exact Hp.
Qed.
Lemma completed_path_nodup__path_exits_head_skip :
  forall words next prev used start path current,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path current ->
    NoDup path /\ ~ In current path.
Proof.
  assert (Hnil : forall next0 start0 current0,
    PathPrefix next0 start0 (@nil Z) current0 -> current0 = start0).
  { intros next0 start0 current0 H0. remember (@nil Z) as p eqn:Heq.
    induction H0; subst; auto.
    apply app_eq_nil in Heq. destruct Heq as [_ Hbad]. discriminate. }
  intros words next prev used start path current Henc Hhead Hpath.
  destruct Hhead as [Hstartb [Hstartu Hstartprev]].
  induction Hpath as [|p cur succ Hp IH Hcur Hedge].
  - split. constructor. intro H. exact H.
  - destruct IH as [Hnd Hfresh].
    assert (Hndfull : NoDup (p ++ cur :: @nil Z)).
    { apply NoDup_app. repeat split.
      - exact Hnd.
      - constructor. intro H. exact H. constructor.
      - intros x Hinx Hinone. simpl in Hinone.
        destruct Hinone as [-> | []]. contradiction. }
    split. exact Hndfull.
    intro Hinsucc.
    apply in_app_or in Hinsucc. destruct Hinsucc as [Hinold | Hinlast].
    + destruct (path_prefix_member_prefix__path_exits_head_skip
        next start p cur succ Hp Hinold)
        as (before & after & Heqp & Hbefore).
      pose proof Hedge as Hedge_outer.
      destruct before as [|a before'].
      * assert (Heqsucc : succ = start) by (apply Hnil with (next0 := next); exact Hbefore).
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used cur start Henc Hcur Hstartb
          (eq_trans Hedge_outer Heqsucc)) as Hbad.
        rewrite Hstartprev in Hbad. lia.
      * inversion Hbefore as [|prefix pred target Hprefix Hpredbound Hedgepred Heqpath].
        pose proof (path_prefix_member_bounds__path_exits_head_skip
          next start p cur succ Hp Hinold) as Hsucc.
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used cur succ Henc Hcur Hsucc Hedge_outer) as Hprev1.
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used pred succ Henc Hpredbound Hsucc Hedgepred) as Hprev2.
        assert (Heqpred : pred = cur) by congruence.
        apply Hfresh. rewrite Heqp.
        rewrite <- Heqpred. apply in_or_app. left. rewrite <- Heqpath.
        apply in_or_app. right. simpl. auto.
    + simpl in Hinlast. destruct Hinlast as [Heq | []].
      assert (Hedge_self : Znth cur next (-1) = cur) by congruence.
      destruct p as [|a p'].
      * assert (Heqcur : cur = start) by
          (apply Hnil with (next0 := next); exact Hp).
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used cur start Henc Hcur Hstartb
          (eq_trans Hedge_self Heqcur)) as Hbad.
        rewrite Hstartprev in Hbad. lia.
      * inversion Hp as [|prefix pred target Hprefix Hpredbound Hedgepred Heqpath].
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used pred cur Henc Hpredbound Hcur Hedgepred) as Hprev1.
        pose proof (encoded_next_prev__path_exits_head_skip
          words next prev used cur cur Henc Hcur Hcur Hedge_self) as Hprev2.
        assert (Heqpred : pred = cur) by congruence.
        apply Hfresh. rewrite <- Heqpred. rewrite <- Heqpath.
        apply in_or_app. right. simpl. auto.
Qed.
Lemma mapped_path_nodup__path_exits_head_skip :
  forall (path : list Z),
    NoDup path -> NoDup (map (fun c => 97 + c) path).
Proof.
  intros path Hnd. induction Hnd.
  - constructor.
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as (y & Heq & Hiny).
      change (97 + y = 97 + x) in Heq.
      apply Z.add_reg_l in Heq. subst y. contradiction.
    + exact IHHnd.
Qed.
Lemma completed_path_disjoint_output__path_exits_head_skip :
  forall words next prev used start path visited_before output_before,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path (-1) ->
    CompletedHeadSet next prev used start visited_before ->
    OutputMatchesVisited visited_before output_before ->
    forall x, In x path -> ~ In (97 + x) output_before.
Proof.
  intros words next prev used start path visited_before output_before
    Henc Hhead Hpath Hcompleted Houtput x Hinx Hinout.
  unfold CompletedHeadSet in Hcompleted.
  destruct Hcompleted as [Hbool Hcompleted].
  unfold OutputMatchesVisited in Houtput.
  destruct Houtput as [Hndout Houtput].
  pose proof (path_prefix_member_bounds__path_exits_head_skip
    next start path (-1) x Hpath Hinx) as Hx.
  apply (proj2 (Houtput x Hx)) in Hinout.
  apply (proj1 (Hcompleted x Hx)) in Hinout.
  destruct Hinout as (old_head & Holdlt & Holdhead & Holdreach).
  destruct (path_prefix_member_prefix__path_exits_head_skip
    next start path (-1) x Hpath Hinx)
    as (before & after & Heq & Hbefore).
  pose proof (head_reaching_path_current_unique__path_exits_head_skip
    words next prev used start before x old_head Henc Hhead Holdhead
    Hbefore Holdreach) as Heqhead.
  lia.
Qed.
Lemma completed_head_set_add_path__path_exits_head_skip :
  forall words next prev used start path visited_before visited_after,
    EncodesGraph words next prev used -> 0 <= start < 26 ->
    IsHead prev used start -> PathPrefix next start path (-1) ->
    CompletedHeadSet next prev used start visited_before ->
    MarkedPath visited_before path visited_after ->
    CompletedHeadSet next prev used (start + 1) visited_after.
Proof.
  intros words next prev used start path visited_before visited_after
    Henc Hstart Hhead Hpath Hcompleted Hmarked.
  unfold CompletedHeadSet in *.
  destruct Hcompleted as [Hbeforebool Hcompleted].
  unfold MarkedPath in Hmarked.
  destruct Hmarked as [Hbeforebool' [Hafterbool Hmarked]].
  split. exact Hafterbool.
  intros c Hc. rewrite Hmarked by exact Hc.
  split.
  - intros [Hbefore | Hinpath].
    + apply (proj1 (Hcompleted c Hc)) in Hbefore.
      destruct Hbefore as (head & Hlt & Hhead0 & Hreach).
      exists head. split. lia. split; assumption.
    + exists start. split. lia. split. exact Hhead.
      apply path_prefix_member_reach__path_exits_head_skip
        with (path := path) (current := -1); assumption.
  - intros (head & Hlt & Hhead0 & Hreach).
    assert (head < start \/ head = start) by lia.
    destruct H as [Hold | ->].
    + left. apply (proj2 (Hcompleted c Hc)).
      exists head. split. lia. split; assumption.
    + right. eapply reachable_in_completed_path__path_exits_head_skip
        with (next := next) (start := start) (target := c) (path := path);
        eauto.
Qed.
Lemma output_matches_visited_add_path__path_exits_head_skip :
  forall words next prev used start path visited_before visited_after output_before,
    EncodesGraph words next prev used -> IsHead prev used start ->
    PathPrefix next start path (-1) ->
    CompletedHeadSet next prev used start visited_before ->
    OutputMatchesVisited visited_before output_before ->
    MarkedPath visited_before path visited_after ->
    OutputMatchesVisited visited_after
      (output_before ++ map (fun c => 97 + c) path).
Proof.
  intros words next prev used start path visited_before visited_after output_before
    Henc Hhead Hpath Hcompleted Houtput Hmarked.
  unfold OutputMatchesVisited in *.
  destruct Houtput as [Hndout Houtput].
  unfold MarkedPath in Hmarked.
  destruct Hmarked as [Hbeforebool [Hafterbool Hmarked]].
  split.
  - apply NoDup_app. repeat split.
    + exact Hndout.
    + apply mapped_path_nodup__path_exits_head_skip.
      apply (proj1 (completed_path_nodup__path_exits_head_skip
        words next prev used start path (-1) Henc Hhead Hpath)).
    + intros y Hinyout Hinymap.
      apply in_map_iff in Hinymap.
      destruct Hinymap as (x & Heq & Hinx).
      change (97 + x = y) in Heq.
      subst y.
      apply (completed_path_disjoint_output__path_exits_head_skip
        words next prev used start path visited_before output_before
        Henc Hhead Hpath Hcompleted (conj Hndout Houtput) x Hinx).
      exact Hinyout.
  - intros c Hc. rewrite Hmarked by exact Hc.
    rewrite in_app_iff. rewrite <- Houtput by exact Hc.
    split.
    + intros [Hbefore | Hinpath]. left. exact Hbefore.
      right. apply in_map. exact Hinpath.
    + intros [Hbefore | Hinmap]. left. exact Hbefore.
      right. apply in_map_iff in Hinmap.
      destruct Hinmap as (x & Heq & Hinx).
      change (97 + x = 97 + c) in Heq.
      apply Z.add_reg_l in Heq. subst x. exact Hinx.
Qed.
Lemma path_scan_finish_to_traversal__path_exits_head_skip :
  forall words next prev used start visited output,
    EncodesGraph words next prev used -> 0 <= start < 26 ->
    PathScanState next prev used start (-1) visited output ->
    TraversalState next prev used (start + 1) visited output.
Proof.
  intros words next prev used start visited output Henc Hstart Hscan.
  unfold PathScanState in Hscan.
  destruct Hscan as (visited_before & output_before & path &
    Htraversal & Hhead & Hpath & Hmarked & Houtput & Hcurrent).
  unfold TraversalState in Htraversal.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  subst output.
  unfold TraversalState. refine (conj _ (conj _ _)).
  - eapply completed_head_set_add_path__path_exits_head_skip; eauto.
  - eapply output_matches_visited_add_path__path_exits_head_skip; eauto.
  - apply ordered_traversal_head; assumption.
Qed.
Lemma traversal_state_skip_nonhead__path_exits_head_skip :
  forall next prev used start visited output,
    0 <= start < 26 ->
    TraversalState next prev used start visited output ->
    (Znth start used 0 = 0 \/ Znth start prev (-1) <> -1) ->
    TraversalState next prev used (start + 1) visited output.
Proof.
  intros next prev used start visited output Hstart Hstate Hreason.
  unfold TraversalState in Hstate.
  destruct Hstate as [Hcompleted [Hmatches Hordered]].
  assert (Hnonhead : ~ IsHead prev used start).
  { intros (_ & Hused & Hprev).
    destruct Hreason as [Hzero | Hnotprev].
    - congruence.
    - contradiction. }
  unfold TraversalState.
  split.
  - unfold CompletedHeadSet in *.
    destruct Hcompleted as [Hbool Hcompleted].
    split. exact Hbool.
    intros c Hc. rewrite Hcompleted by exact Hc.
    split.
    + intros (head & Hlt & Hhead & Hreach).
      exists head. split. lia. split; assumption.
    + intros (head & Hlt & Hhead & Hreach).
      assert (head < start \/ head = start) by lia.
      destruct H as [Hold | Heq].
      * exists head. split. lia. split; assumption.
      * subst head. exfalso. apply Hnonhead. exact Hhead.
  - split. exact Hmatches.
    apply ordered_traversal_skip; assumption.
Qed.
Lemma path_scan_finish_head__traversal_closure :
  forall words next prev used start visited output,
    EncodesGraph words next prev used -> 0 <= start < 26 ->
    PathScanState next prev used start (-1) visited output ->
    TraversalState next prev used (start + 1) visited output.
Proof.
  intros words next prev used start visited output Henc Hstart Hscan.
  eapply path_scan_finish_to_traversal__path_exits_head_skip; eauto.
Qed.
Lemma traversal_state_skip_nonhead__traversal_closure :
  forall next prev used start visited output,
    0 <= start < 26 ->
    TraversalState next prev used start visited output ->
    (Znth start used 0 = 0 \/ Znth start prev (-1) <> -1) ->
    TraversalState next prev used (start + 1) visited output.
Proof.
  intros next prev used start visited output Hstart Hstate Hreason.
  eapply traversal_state_skip_nonhead__path_exits_head_skip; eauto.
Qed.
Lemma coverage_scan_step__coverage_scan :
  forall used visited checked,
    CoverageScanState used visited checked ->
    0 <= checked < 26 ->
    (Znth checked used 0 = 0 \/
      (Znth checked used 0 <> 0 /\ Znth checked visited 0 <> 0)) ->
    CoverageScanState used visited (checked + 1).
Proof.
  intros used visited checked Hscan Hchecked Hcurrent.
  unfold CoverageScanState, BooleanArray in *.
  destruct Hscan as [[Hused_len Hused_bool]
    [[Hvisited_len Hvisited_bool] Hold]].
  split.
  - split; assumption.
  - split.
    + split; assumption.
    + intros c Hc Hused_c.
      destruct (Z_lt_ge_dec c checked) as [Hlt | Hge].
      * apply Hold; lia.
      * assert (c = checked) by lia.
        subst c.
        destruct Hcurrent as [Hused_zero | [Hused_nonzero Hvisited_nonzero]].
        -- congruence.
        -- specialize (Hvisited_bool checked Hchecked).
           destruct Hvisited_bool; congruence.
Qed.
Lemma nodup_pivot_unique__final_success :
  forall (l before1 before2 after1 after2 : list Z) (x : Z),
    NoDup l ->
    l = before1 ++ x :: after1 ->
    l = before2 ++ x :: after2 ->
    before1 = before2 /\ after1 = after2.
Proof.
  intros l before1 before2 after1 after2 x Hnodup H1 H2.
  assert (Hbefore1 : ~ In x before1).
  { intro Hin.
    pose proof (NoDup_remove_2 before1 after1 x) as Hremove.
    apply Hremove.
    - rewrite <- H1. exact Hnodup.
    - apply in_or_app. left. exact Hin. }
  assert (Hafter1 : ~ In x after1).
  { intro Hin.
    pose proof (NoDup_remove_2 before1 after1 x) as Hremove.
    apply Hremove.
    - rewrite <- H1. exact Hnodup.
    - apply in_or_app. right. exact Hin. }
  assert (Hbefore2 : ~ In x before2).
  { intro Hin.
    pose proof (NoDup_remove_2 before2 after2 x) as Hremove.
    apply Hremove.
    - rewrite <- H2. exact Hnodup.
    - apply in_or_app. left. exact Hin. }
  assert (Hafter2 : ~ In x after2).
  { intro Hin.
    pose proof (NoDup_remove_2 before2 after2 x) as Hremove.
    apply Hremove.
    - rewrite <- H2. exact Hnodup.
    - apply in_or_app. right. exact Hin. }
  pose proof (app_inj_pivot before1 after1 before2 after2 x
    (eq_trans (eq_sym H1) H2)) as Hpivot.
  destruct Hpivot as [[[_ Hin] | [Hin _]] | Heq].
  - exact (False_ind _ (Hafter2 Hin)).
  - exact (False_ind _ (Hafter1 Hin)).
  - exact Heq.
Qed.
Lemma consecutive_chain_occurs__final_success :
  forall (word text : list Z),
    word <> [] ->
    NoDup text ->
    (forall x, In x word -> In x text) ->
    (forall prefix x y suffix,
      word = prefix ++ x :: y :: suffix ->
      (exists before after, text = before ++ x :: y :: after)) ->
    OccursContiguously word text.
Proof.
  induction word as [|x tail IH]; intros text Hnonempty Hnodup Hinclusion Hadj.
  { contradiction. }
  destruct tail as [|y rest].
  - unfold OccursContiguously.
    pose proof (Hinclusion x (or_introl eq_refl)) as Hinx.
    apply in_split in Hinx.
    destruct Hinx as [before [after Htext]].
    exists before, after. simpl. exact Htext.
  - assert (Hxy : exists before after, text = before ++ x :: y :: after).
    { apply (Hadj [] x y rest). reflexivity. }
    assert (Htail : OccursContiguously (y :: rest) text).
    { apply IH.
      - discriminate.
      - exact Hnodup.
      - intros z Hz. apply Hinclusion. right. exact Hz.
      - intros prefix z1 z2 suffix Heq.
        apply (Hadj (x :: prefix) z1 z2 suffix).
        simpl. rewrite Heq. reflexivity. }
    unfold OccursContiguously in Htail.
    destruct Hxy as [before1 [after1 Htext1]].
    destruct Htail as [before2 [after2 Htext2]].
    assert (Hpivot := nodup_pivot_unique__final_success
      text (before1 ++ [x]) before2 after1 (rest ++ after2) y Hnodup).
    destruct Hpivot as [Hbefore Hafter].
    { rewrite <- app_assoc. simpl. exact Htext1. }
    { simpl. exact Htext2. }
    unfold OccursContiguously.
    exists before1, after2.
    rewrite Htext1, Hafter. reflexivity.
Qed.
Lemma path_prefix_consecutive_or_last__final_success :
  forall next start path endpoint x y,
    PathPrefix next start path endpoint ->
    In x path ->
    Znth x next (-1) = y ->
    (exists before after, path = before ++ x :: y :: after) \/
      exists before, path = before ++ [x] /\ endpoint = y.
Proof.
  intros next start path endpoint x y Hpath.
  induction Hpath as [| path current successor Hprefix IH Hcurrent Hnext];
    intros Hin Hxy.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + specialize (IH Hin Hxy).
      destruct IH as [Hconsecutive | [before [Hbefore Hend]]].
      * left.
        destruct Hconsecutive as [leftpart [rightpart Heq]].
        exists leftpart, (rightpart ++ [current]).
        rewrite Heq, <- app_assoc. reflexivity.
      * left.
        exists before, [].
        subst current. rewrite Hbefore, <- app_assoc. reflexivity.
    + simpl in Hin. destruct Hin as [Hin | Hin]; [|contradiction].
      subst current.
      right. exists path. split; [reflexivity|].
      rewrite Hxy in Hnext. symmetry. exact Hnext.
Qed.
Lemma path_prefix_consecutive__final_success :
  forall next start path x y,
    PathPrefix next start path (-1) ->
    In x path ->
    Znth x next (-1) = y ->
    0 <= y ->
    exists before after, path = before ++ x :: y :: after.
Proof.
  intros next start path x y Hpath Hin Hnext Hy.
  destruct (path_prefix_consecutive_or_last__final_success
    next start path (-1) x y Hpath Hin Hnext) as [H | [before [_ Hend]]].
  - exact H.
  - lia.
Qed.
Lemma ordered_traversal_output_bounds__final_success :
  forall next prev used bound output ch,
    OrderedTraversal next prev used bound output ->
    In ch output ->
    exists c, 0 <= c < 26 /\ ch = 97 + c.
Proof.
  intros next prev used bound output ch Htrav.
  induction Htrav as
    [|bound output Htrav IH Hbound Hskip
     |bound output path Htrav IH Hbound Hhead Hpath]; intros Hin.
  - contradiction.
  - apply IH. exact Hin.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply IH. exact Hin.
    + apply in_map_iff in Hin.
      destruct Hin as [c [Hch Hinc]].
      exists c. split; [|symmetry; exact Hch].
      clear Htrav IH Hhead Hch.
      induction Hpath.
      * contradiction.
      * apply in_app_or in Hinc. destruct Hinc as [Hinc | Hinc].
        -- apply IHHpath. exact Hinc.
        -- simpl in Hinc. destruct Hinc as [Hinc | Hinc]; [subst; assumption|contradiction].
Qed.
Lemma ordered_traversal_consecutive__final_success :
  forall next prev used bound output x y,
    OrderedTraversal next prev used bound output ->
    In (97 + x) output ->
    Znth x next (-1) = y ->
    0 <= y < 26 ->
    exists before after, output = before ++ (97 + x) :: (97 + y) :: after.
Proof.
  intros next prev used bound output x y Htrav.
  induction Htrav as
    [|bound output Htrav IH Hbound Hskip
     |bound output path Htrav IH Hbound Hhead Hpath];
    intros Hin Hnext Hy.
  - contradiction.
  - apply IH; assumption.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + specialize (IH Hin Hnext Hy).
      destruct IH as [before [after Heq]].
      exists before, (after ++ map (fun c => 97 + c) path).
      rewrite Heq, <- app_assoc. reflexivity.
    + apply in_map_iff in Hin.
      destruct Hin as [z [Hz Hin]].
      assert (z = x) by lia. subst z.
      pose proof (path_prefix_consecutive__final_success
        next bound path x y Hpath Hin Hnext (proj1 Hy)) as Hconsecutive.
      destruct Hconsecutive as [before [after Heq]].
      exists (output ++ map (fun c => 97 + c) before),
        (map (fun c => 97 + c) after).
      rewrite Heq, !map_app. simpl. rewrite app_assoc. reflexivity.
Qed.
Lemma Znth_in_bounds__final_success :
  forall (l : list Z) i d,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  induction l as [|a l IH]; intros i d Hbound.
  - unfold Zlength in Hbound. simpl in Hbound. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. left. reflexivity.
    + right. rewrite Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hbound. lia.
Qed.
Lemma next_reach_used__final_success :
  forall words next prev used start target,
    EncodesGraph words next prev used ->
    Znth start used 0 = 1 ->
    0 <= start < 26 ->
    NextReach next start target ->
    0 <= target < 26 ->
    Znth target used 0 = 1.
Proof.
  intros words next prev used start target Hgraph Hstart Hstartbound Hreach.
  revert Hstart Hstartbound.
  induction Hreach as [c | from mid to Hnext Hmid Hreach IH];
    intros Hused Hbound Htarget.
  - exact Hused.
  - apply IH; try assumption.
    destruct Hgraph as [_ [_ [_ [_ [Husediff [Hnextiff _]]]]]].
    apply (proj2 (Husediff mid Hmid)).
    unfold UsedInWords.
    apply (proj1 (Hnextiff from mid Hbound Hmid)) in Hnext.
    unfold AdjacentInWords in Hnext.
    destruct Hnext as [word [i [Hinword [Hi [Hilen [_ Hright]]]]]].
    exists word. split; [exact Hinword|].
    rewrite <- Hright.
    apply Znth_in_bounds__final_success. lia.
Qed.
Lemma adjacent_in_words_of_decomposition__final_success :
  forall words word prefix x y suffix,
    In word words ->
    word = prefix ++ x :: y :: suffix ->
    AdjacentInWords words x y.
Proof.
  intros words word prefix x y suffix Hinword Hword.
  unfold AdjacentInWords.
  exists word, (Zlength prefix).
  subst word.
  split; [exact Hinword|].
  split.
  - apply Zlength_nonneg.
  - split.
    + pose proof (Zlength_nonneg suffix).
      rewrite Zlength_app, !Zlength_cons. lia.
    + split.
      * rewrite app_Znth2 by lia.
        replace (Zlength prefix - Zlength prefix) with 0 by lia.
        apply Znth0_cons.
      * rewrite app_Znth2 by lia.
        replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
        rewrite Znth_cons by lia. apply Znth0_cons.
Qed.
Lemma used_letter_in_output__final_success :
  forall words next prev used visited output ch,
    EncodesGraph words next prev used ->
    CoverageScanState used visited 26 ->
    OutputMatchesVisited visited output ->
    97 <= ch <= 122 ->
    UsedInWords words ch ->
    In ch output.
Proof.
  intros words next prev used visited output ch Hgraph Hcoverage Hmatches
    Hlower Hused.
  destruct Hgraph as [_ [_ [_ [_ [Husediff _]]]]].
  destruct Hcoverage as [_ [_ Hcovered]].
  destruct Hmatches as [_ Hmatches].
  set (c := ch - 97).
  assert (Hcbound : 0 <= c < 26) by (unfold c; lia).
  assert (Husedvalue : Znth c used 0 = 1).
  { apply (proj2 (Husediff c Hcbound)).
    replace (97 + c) with ch by (unfold c; lia). exact Hused. }
  assert (Hvisited : Znth c visited 0 = 1).
  { apply Hcovered; [exact Hcbound|exact Husedvalue]. }
  apply (proj1 (Hmatches c Hcbound)) in Hvisited.
  replace (97 + c) with ch in Hvisited by (unfold c; lia).
  exact Hvisited.
Qed.
Lemma output_letter_used__final_success :
  forall words next prev used visited output ch,
    EncodesGraph words next prev used ->
    TraversalState next prev used 26 visited output ->
    In ch output ->
    UsedInWords words ch.
Proof.
  intros words next prev used visited output ch Hgraph Htraversal Hin.
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  destruct (ordered_traversal_output_bounds__final_success
    next prev used 26 output ch Hordered Hin) as [c [Hcbound Hch]].
  subst ch.
  destruct Hmatches as [_ Hmatches].
  apply (proj2 (Hmatches c Hcbound)) in Hin.
  destruct Hcompleted as [_ Hcompleted].
  apply (proj1 (Hcompleted c Hcbound)) in Hin.
  destruct Hin as [head [Hheadbound [Hishead Hreach]]].
  destruct Hishead as [Hheadrange [Hheadused _]].
  assert (Htargetused : Znth c used 0 = 1).
  { eapply next_reach_used__final_success; eauto. }
  destruct Hgraph as [_ [_ [_ [_ [Husediff _]]]]].
  apply (proj1 (Husediff c Hcbound)) in Htargetused.
  exact Htargetused.
Qed.
Lemma successful_traversal_from_complete_coverage__final_success :
  forall given next prev used visited output,
    Pre given ->
    EncodesGraph given next prev used ->
    TraversalState next prev used 26 visited output ->
    CoverageScanState used visited 26 ->
    GoodRestoration given output.
Proof.
  intros given next prev used visited output Hpre Hgraph Htraversal Hcoverage.
  destruct Hpre as [Hgivenlength Hwords].
  destruct Htraversal as [Hcompleted [Hmatches Hordered]].
  destruct Hmatches as [Hnodup Hmatches].
  unfold GoodRestoration.
  split; [exact Hnodup|].
  split.
  - intros ch. split.
    + intro Hin.
      change (UsedInWords given ch).
      apply (output_letter_used__final_success
        given next prev used visited output ch Hgraph).
      * unfold TraversalState. split; [exact Hcompleted|].
        split; [split; [exact Hnodup|exact Hmatches]|exact Hordered].
      * exact Hin.
    + intros [word [Hinword Hinwordch]].
      apply (used_letter_in_output__final_success
        given next prev used visited output ch Hgraph Hcoverage).
      * split; [exact Hnodup|exact Hmatches].
      * apply Forall_forall with (x := word) in Hwords; [|exact Hinword].
        destruct Hwords as [_ Hletters].
        apply Forall_forall with (x := ch) in Hletters; [|exact Hinwordch].
        exact Hletters.
      * exists word. split; assumption.
  - intros word Hinword.
    assert (Hwordprops := Hwords).
    apply Forall_forall with (x := word) in Hwordprops; [|exact Hinword].
    destruct Hwordprops as [Hwordnonempty Hletters].
    apply consecutive_chain_occurs__final_success.
    + intro Heq. subst word. unfold Zlength in Hwordnonempty.
      simpl in Hwordnonempty. lia.
    + exact Hnodup.
    + intros ch Hinch.
      apply (used_letter_in_output__final_success
        given next prev used visited output ch Hgraph Hcoverage).
      * split; [exact Hnodup|exact Hmatches].
      * apply Forall_forall with (x := ch) in Hletters; assumption.
      * exists word. split; assumption.
    + intros prefix x y suffix Hdecomp.
      assert (Hxlower : LowercaseLetter x).
      { apply Forall_forall with (x := x) in Hletters.
        - exact Hletters.
        - rewrite Hdecomp. apply in_or_app. right. simpl. auto. }
      assert (Hylower : LowercaseLetter y).
      { apply Forall_forall with (x := y) in Hletters.
        - exact Hletters.
        - rewrite Hdecomp. apply in_or_app. right. simpl. auto. }
      unfold LowercaseLetter in Hxlower, Hylower.
      assert (Hadj : AdjacentInWords given x y).
      { eapply adjacent_in_words_of_decomposition__final_success; eauto. }
      pose proof Hgraph as Hgraph_for_next.
      destruct Hgraph_for_next as [_ [_ [_ [_ [_ [Hnextiff _]]]]]].
      set (left := x - 97).
      set (right := y - 97).
      assert (Hleft : 0 <= left < 26) by (unfold left; lia).
      assert (Hright : 0 <= right < 26) by (unfold right; lia).
      assert (Hnext : Znth left next (-1) = right).
      { apply (proj2 (Hnextiff left right Hleft Hright)).
        replace (97 + left) with x by (unfold left; lia).
        replace (97 + right) with y by (unfold right; lia).
        exact Hadj. }
      pose proof (ordered_traversal_consecutive__final_success
        next prev used 26 output left right Hordered) as Hconsecutive.
      replace (97 + left) with x in Hconsecutive by (unfold left; lia).
      replace (97 + right) with y in Hconsecutive by (unfold right; lia).
      apply Hconsecutive; [|exact Hnext|exact Hright].
      apply (used_letter_in_output__final_success
        given next prev used visited output x Hgraph Hcoverage).
      * split; [exact Hnodup|exact Hmatches].
      * exact Hxlower.
      * exists word. split; [exact Hinword|].
        rewrite Hdecomp. apply in_or_app. right. simpl. auto.
Qed.
Lemma covered_traversal_good_restoration__successful_traversal :
  forall given next prev used visited output,
    Pre given ->
    EncodesGraph given next prev used ->
    TraversalState next prev used 26 visited output ->
    CoverageScanState used visited 26 ->
    GoodRestoration given output.
Proof.
  intros given next prev used visited output Hpre Hgraph Htraversal Hcoverage.
  eapply successful_traversal_from_complete_coverage__final_success; eauto.
Qed.
Lemma nodup_Znth_injective__cycle_failure_return :
  forall {A : Type} (default : A) (xs : list A) i j,
    NoDup xs ->
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth i xs default = Znth j xs default ->
    i = j.
Proof.
  intros A default xs i j Hnodup Hi Hj Heq.
  unfold Znth in Heq.
  rewrite Zlength_correct in Hi, Hj.
  pose proof
    ((proj1 (NoDup_nth xs default)) Hnodup
      (Z.to_nat i) (Z.to_nat j) ltac:(lia) ltac:(lia) Heq) as Hij.
  lia.
Qed.
Lemma adjacent_in_words_has_ordered_indices__cycle_failure_return :
  forall words text x y,
    (forall word, In word words -> OccursContiguously word text) ->
    AdjacentInWords words x y ->
    exists il ir,
      0 <= il < ir /\ ir < Zlength text /\
      Znth il text 0 = x /\ Znth ir text 0 = y.
Proof.
  intros words text x y Hocc Hadj.
  destruct Hadj as [word [i [Hin [Hi0 [Hi1 [Hleft Hright]]]]]].
  destruct (Hocc word Hin) as [before [suffix Htext]].
  subst text.
  pose proof (Zlength_nonneg before).
  pose proof (Zlength_nonneg word).
  pose proof (Zlength_nonneg suffix).
  exists (Zlength before + i), (Zlength before + i + 1).
  rewrite !Zlength_app.
  repeat split; try lia.
  - rewrite app_Znth2 by lia.
    replace (Zlength before + i - Zlength before) with i by lia.
    rewrite app_Znth1 by lia.
    exact Hleft.
  - rewrite app_Znth2 by lia.
    replace (Zlength before + i + 1 - Zlength before) with (i + 1) by lia.
    rewrite app_Znth1 by lia.
    exact Hright.
Qed.
Lemma next_reach_snoc__cycle_failure_return :
  forall next head from to,
    NextReach next head from ->
    Znth from next (-1) = to ->
    0 <= to < 26 ->
    NextReach next head to.
Proof.
  intros next head from to Hreach Hedge Hto.
  induction Hreach.
  - eapply next_reach_step.
    + exact Hedge.
    + exact Hto.
    + apply next_reach_refl.
  - eapply next_reach_step; eauto.
Qed.
Lemma good_restoration_index_reachable__cycle_failure_return :
  forall words text next prev used i c,
    EncodesGraph words next prev used ->
    GoodRestoration words text ->
    0 <= i < Zlength text ->
    0 <= c < 26 ->
    Znth i text 0 = 97 + c ->
    exists head, IsHead prev used head /\ NextReach next head c.
Proof.
  intros words text next prev used i c Henc Hgood Hi Hc Hchar.
  assert (Hi_nonneg : 0 <= i) by lia.
  revert c Hi Hc Hchar.
  pattern i.
  apply Z_lt_induction; [|exact Hi_nonneg].
  intros i0 IH c Hi Hc Hchar.
  destruct Henc as
    [Hcompat [Hnext [Hprev [Hused [HusedWords [HnextAdj HprevAdj]]]]]].
  destruct Hgood as [Hnodup [Hmembers Hocc]].
  destruct Hprev as [HprevLen HprevBounds].
  pose proof (HprevBounds c Hc) as Hpc.
  set (p := Znth c prev (-1)) in *.
  destruct (Z.eq_dec p (-1)) as [Hpminus | Hpnotminus].
  - exists c.
    split.
    + unfold IsHead.
      split; [exact Hc|].
      split.
      * apply (proj2 (HusedWords c Hc)).
        apply (proj1 (Hmembers (97 + c))).
        unfold Znth in Hchar.
        rewrite <- Hchar.
        apply nth_In.
        rewrite Zlength_correct in Hi. lia.
      * exact Hpminus.
    + apply next_reach_refl.
  - assert (Hp : 0 <= p < 26) by lia.
    assert (Hadj : AdjacentInWords words (97 + p) (97 + c)).
    { apply (proj1 (HprevAdj p c Hp Hc)). exact (eq_sym (eq_refl p)). }
    destruct (adjacent_in_words_has_ordered_indices__cycle_failure_return
      words text (97 + p) (97 + c) Hocc Hadj)
      as [ip [ic [[Hip0 Hipic] [Hiclen [Hipchar Hicchar]]]]].
    assert (Hic : ic = i0).
    { eapply nodup_Znth_injective__cycle_failure_return with (default := 0).
      - exact Hnodup.
      - lia.
      - exact Hi.
      - congruence. }
    subst ic.
    destruct (IH ip ltac:(lia) p ltac:(lia) Hp Hipchar)
      as [head [Hhead Hreach]].
    exists head.
    split; [exact Hhead|].
    eapply next_reach_snoc__cycle_failure_return; eauto.
    apply (proj2 (HnextAdj p c Hp Hc)).
    exact Hadj.
Qed.
Lemma used_unvisited_no_restoration__cycle_failure_return :
  forall words next prev used visited output c,
    EncodesGraph words next prev used ->
    TraversalState next prev used 26 visited output ->
    0 <= c < 26 ->
    Znth c used 0 <> 0 ->
    Znth c visited 0 = 0 ->
    forall text, ~ GoodRestoration words text.
Proof.
  intros words next prev used visited output c Henc Htrav Hc Husednz Hvis0
    text Hgood.
  pose proof Henc as Henc'.
  destruct Henc as
    [Hcompat [Hnext [Hprev [Hused [HusedWords [HnextAdj HprevAdj]]]]]].
  destruct Hused as [HusedLen HusedBool].
  assert (Hused1 : Znth c used 0 = 1).
  { destruct (HusedBool c Hc); congruence. }
  assert (Hin : In (97 + c) text).
  { apply (proj2 (proj1 (proj2 Hgood) (97 + c))).
    apply (proj1 (HusedWords c Hc)). exact Hused1. }
  destruct (In_nth text (97 + c) 0 Hin) as [n [Hn Hnth]].
  assert (Hi : 0 <= Z.of_nat n < Zlength text).
  { rewrite Zlength_correct. lia. }
  assert (Hchar : Znth (Z.of_nat n) text 0 = 97 + c).
  { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  destruct (good_restoration_index_reachable__cycle_failure_return
    words text next prev used (Z.of_nat n) c Henc' Hgood Hi Hc Hchar)
    as [head [Hhead Hreach]].
  destruct Htrav as [[HvisBool HvisHeads] [Hout Hord]].
  assert (Hvis1 : Znth c visited 0 = 1).
  { apply (proj2 (HvisHeads c Hc)).
    exists head.
    split.
    - destruct Hhead as [[Hhead0 Hhead26] Hheadrest]. lia.
    - split; assumption. }
  congruence.
Qed.
Lemma occurs_adjacent_position__word_failure_returns :
  forall word text left right i,
    OccursContiguously word text ->
    0 <= i -> i + 1 < Zlength word ->
    Znth i word 0 = left -> Znth (i + 1) word 0 = right ->
    exists p : nat,
      nth_error text p = Some left /\
      nth_error text (S p) = Some right.
Proof.
  intros word text left right i Hocc Hi Hbound Hleft Hright.
  rewrite Zlength_correct in Hbound.
  destruct Hocc as [before [after ->]].
  assert (Hinat : (Z.to_nat i < length word)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  assert (Hinextnat : (Z.to_nat (i + 1) < length word)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  exists (length before + Z.to_nat i)%nat.
  split.
  - rewrite nth_error_app2 by lia.
    replace (length before + Z.to_nat i - length before)%nat
      with (Z.to_nat i) by lia.
    rewrite (nth_error_app1 word after Hinat).
    rewrite (nth_error_nth' word 0 (n := Z.to_nat i) Hinat).
    unfold Znth in Hleft. now rewrite Hleft.
  - replace (S (length before + Z.to_nat i))
      with (length before + Z.to_nat (i + 1))%nat by lia.
    rewrite nth_error_app2 by lia.
    replace (length before + Z.to_nat (i + 1) - length before)%nat
      with (Z.to_nat (i + 1)) by lia.
    rewrite (nth_error_app1 word after Hinextnat).
    rewrite (nth_error_nth' word 0 (n := Z.to_nat (i + 1)) Hinextnat).
    unfold Znth in Hright. now rewrite Hright.
Qed.
Lemma good_restoration_word_nodup__word_failure_returns :
  forall words text word,
    GoodRestoration words text ->
    In word words ->
    NoDup word.
Proof.
  intros words text word [Hnodup [_ Hoccurs]] Hin.
  destruct (Hoccurs word Hin) as [before [after Heq]].
  rewrite Heq in Hnodup.
  pose proof (NoDup_app_remove_l before (word ++ after) Hnodup) as Htail.
  exact (NoDup_app_remove_r word after Htail).
Qed.
Lemma in_prefix_witness__word_failure_returns :
  forall (word : list Z) i x,
    0 <= i <= Zlength word ->
    In x (sublist 0 i word) ->
    exists j, 0 <= j < i /\ Znth j word 0 = x.
Proof.
  intros word i x Hi Hin.
  apply In_nth_error in Hin. destruct Hin as [j Hj].
  exists (Z.of_nat j).
  assert (Hjbound : (j < length (sublist 0 i word))%nat).
  { apply nth_error_Some. rewrite Hj. discriminate. }
  split.
  - rewrite sublist_length in Hjbound by lia. lia.
  - assert (Hnat : nth j (sublist 0 i word) 0 = x).
    { eapply nth_error_nth. exact Hj. }
    assert (Hjz : 0 <= Z.of_nat j < i).
    { rewrite sublist_length in Hjbound by lia. lia. }
    assert (Hprefix : Znth (Z.of_nat j) (sublist 0 i word) 0 = x).
    { unfold Znth. rewrite Nat2Z.id. exact Hnat. }
    rewrite Znth_sublist0 in Hprefix by exact Hjz. exact Hprefix.
Qed.
Lemma duplicate_scanned_character_no_restoration__word_failure_returns :
  forall g z i next prev used seen last cur,
    WordScanState g z i next prev used seen last ->
    0 <= z < Zlength g ->
    0 <= i <= Zlength (Znth z g (@nil Z)) ->
    0 <= cur < 26 ->
    i < Zlength (Znth z g (@nil Z)) ->
    Znth i (Znth z g (@nil Z)) 0 = 97 + cur ->
    Znth cur seen 0 <> 0 ->
    Spec g None.
Proof.
  intros g z i next prev used seen last cur Hstate Hz Hi Hcurbound Hilt
    Hvaluei Hseen.
  unfold Spec. intros text Hgood.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [_ [Hseenarray [Hseenchar _]]]].
  destruct Hseenarray as [Hseenlen Hseenvalues].
  assert (Hseenone : Znth cur seen 0 = 1).
  { destruct (Hseenvalues cur Hcurbound) as [Hzero | Hone].
    - exfalso. apply Hseen. exact Hzero.
    - exact Hone. }
  pose proof (proj1 (Hseenchar cur Hcurbound) Hseenone) as Hinprefix.
  destruct (in_prefix_witness__word_failure_returns
    (Znth z g (@nil Z)) i (97 + cur) Hi Hinprefix)
    as [j [Hj Hvaluej]].
  assert (Hwordin : In (Znth z g (@nil Z)) g).
  { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
  pose proof (good_restoration_word_nodup__word_failure_returns
    g text (Znth z g (@nil Z)) Hgood Hwordin) as Hnodup.
  pose proof (proj1 (NoDup_nth (Znth z g (@nil Z)) 0) Hnodup
    (Z.to_nat j) (Z.to_nat i)) as Hinjective.
  assert (Hjnat : (Z.to_nat j < length (Znth z g (@nil Z)))%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  assert (Hinat : (Z.to_nat i < length (Znth z g (@nil Z)))%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  specialize (Hinjective Hjnat Hinat).
  unfold Znth in Hvaluej, Hvaluei.
  specialize (Hinjective (eq_trans Hvaluej (eq_sym Hvaluei))).
  apply (f_equal Z.of_nat) in Hinjective.
  rewrite !Z2Nat.id in Hinjective by lia. lia.
Qed.
Lemma adjacent_processed_lift__word_failure_returns :
  forall (g : list (list Z)) (z i left right : Z),
    0 <= z < Zlength g ->
    0 <= i <= Zlength (Znth z g (@nil Z)) ->
    AdjacentInWords
      (sublist 0 z g ++
       cons (sublist 0 i (Znth z g (@nil Z))) (@nil (list Z))) left right ->
    AdjacentInWords g left right.
Proof.
  intros g z i left right Hz Hi Hadj.
  destruct Hadj as [word [j [Hin [Hj [Hjbound [Hleft Hright]]]]]].
  apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - exists word, j. repeat split; try assumption.
    assert (Hg : g = sublist 0 z g ++ sublist z (Zlength g) g).
    { rewrite <- sublist_split by lia. symmetry. apply sublist_self. reflexivity. }
    rewrite Hg. apply in_or_app. now left.
  - destruct Hin as [Heq | Hin]; [subst word | contradiction].
    rewrite Zlength_sublist0 in Hjbound by lia.
    assert (Hjlt : 0 <= j < i) by lia.
    exists (Znth z g (@nil Z)), j. repeat split.
    + unfold Znth. apply nth_In.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia.
    + exact Hj.
    + lia.
    + rewrite Znth_sublist0 in Hleft by exact Hjlt. exact Hleft.
    + rewrite Znth_sublist0 in Hright by lia. exact Hright.
Qed.
Lemma nodup_successor_unique__word_failure_returns :
  forall (text : list Z) (left right1 right2 : Z) (p1 p2 : nat),
    NoDup text ->
    nth_error text p1 = Some left ->
    nth_error text (S p1) = Some right1 ->
    nth_error text p2 = Some left ->
    nth_error text (S p2) = Some right2 ->
    right1 = right2.
Proof.
  intros text left right1 right2 p1 p2 Hnodup Hleft1 Hright1 Hleft2 Hright2.
  assert (Hp1 : (p1 < length text)%nat).
  { apply nth_error_Some. rewrite Hleft1. discriminate. }
  pose proof (proj1 (NoDup_nth_error text) Hnodup p1 p2 Hp1
    (eq_trans Hleft1 (eq_sym Hleft2))) as ->.
  congruence.
Qed.
Lemma good_restoration_outgoing_unique__word_failure_returns :
  forall words text left right1 right2,
    GoodRestoration words text ->
    AdjacentInWords words left right1 ->
    AdjacentInWords words left right2 ->
    right1 = right2.
Proof.
  intros words text left right1 right2 Hgood H1 H2.
  destruct Hgood as [Hnodup [_ Hoccurs]].
  destruct H1 as [word1 [i1 [Hin1 [Hi1 [Hb1 [Hl1 Hr1]]]]]].
  destruct H2 as [word2 [i2 [Hin2 [Hi2 [Hb2 [Hl2 Hr2]]]]]].
  pose proof (Hoccurs word1 Hin1) as Hocc1.
  pose proof (Hoccurs word2 Hin2) as Hocc2.
  destruct (occurs_adjacent_position__word_failure_returns
    word1 text left right1 i1 Hocc1 Hi1 Hb1 Hl1 Hr1)
    as [p1 [Hp1 Hsp1]].
  destruct (occurs_adjacent_position__word_failure_returns
    word2 text left right2 i2 Hocc2 Hi2 Hb2 Hl2 Hr2)
    as [p2 [Hp2 Hsp2]].
  exact (@nodup_successor_unique__word_failure_returns
    text left right1 right2 p1 p2 Hnodup Hp1 Hsp1 Hp2 Hsp2).
Qed.
Lemma nodup_predecessor_unique__word_failure_returns :
  forall (text : list Z) (left1 left2 right : Z) (p1 p2 : nat),
    NoDup text ->
    nth_error text p1 = Some left1 ->
    nth_error text (S p1) = Some right ->
    nth_error text p2 = Some left2 ->
    nth_error text (S p2) = Some right ->
    left1 = left2.
Proof.
  intros text left1 left2 right p1 p2 Hnodup Hl1 Hr1 Hl2 Hr2.
  assert (Hsp1 : (S p1 < length text)%nat).
  { apply nth_error_Some. rewrite Hr1. discriminate. }
  pose proof (proj1 (NoDup_nth_error text) Hnodup (S p1) (S p2) Hsp1
    (eq_trans Hr1 (eq_sym Hr2))) as Heq.
  injection Heq as ->. congruence.
Qed.
Lemma good_restoration_incoming_unique__word_failure_returns :
  forall words text left1 left2 right,
    GoodRestoration words text ->
    AdjacentInWords words left1 right ->
    AdjacentInWords words left2 right ->
    left1 = left2.
Proof.
  intros words text left1 left2 right Hgood H1 H2.
  destruct Hgood as [Hnodup [_ Hoccurs]].
  destruct H1 as [word1 [i1 [Hin1 [Hi1 [Hb1 [Hl1 Hr1]]]]]].
  destruct H2 as [word2 [i2 [Hin2 [Hi2 [Hb2 [Hl2 Hr2]]]]]].
  destruct (occurs_adjacent_position__word_failure_returns
    word1 text left1 right i1 (Hoccurs word1 Hin1) Hi1 Hb1 Hl1 Hr1)
    as [p1 [Hp1 Hsp1]].
  destruct (occurs_adjacent_position__word_failure_returns
    word2 text left2 right i2 (Hoccurs word2 Hin2) Hi2 Hb2 Hl2 Hr2)
    as [p2 [Hp2 Hsp2]].
  exact (@nodup_predecessor_unique__word_failure_returns
    text left1 left2 right p1 p2 Hnodup Hp1 Hsp1 Hp2 Hsp2).
Qed.
Lemma outgoing_conflict_no_restoration__word_failure_returns :
  forall g z i next prev used seen last cur,
    WordScanState g z i next prev used seen last ->
    0 <= z < Zlength g ->
    0 <= i <= Zlength (Znth z g (@nil Z)) ->
    0 <= last < 26 ->
    0 <= cur < 26 ->
    i < Zlength (Znth z g (@nil Z)) ->
    Znth i (Znth z g (@nil Z)) 0 = 97 + cur ->
    Znth last next 0 >= 0 ->
    Znth last next 0 <> cur ->
    Spec g None.
Proof.
  intros g z i next prev used seen last cur Hstate Hz Hi Hlast Hcurbound
    Hilt Hcurvalue Hnextnonneg Hconflict.
  unfold Spec. intros text Hgood.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [Henc [_ [_ Hlaststate]]]].
  destruct Hlaststate as [[-> Hbad] | [Hipos Hlastvalue]]; [lia|].
  set (old := Znth last next 0).
  assert (Hlastchar : Znth (i - 1) (Znth z g (@nil Z)) 0 = 97 + last).
  { rewrite Hlastvalue. lia. }
  assert (Hwordin : In (Znth z g (@nil Z)) g).
  { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
  assert (Hcurrent : AdjacentInWords g (97 + last) (97 + cur)).
  { exists (Znth z g (@nil Z)), (i - 1).
    split; [exact Hwordin|].
    split; [lia|]. split; [lia|].
    split; [exact Hlastchar|].
    replace (i - 1 + 1) with i by lia. exact Hcurvalue. }
  pose proof Henc as Henc0.
  unfold EncodesGraph in Henc0.
  destruct Henc0 as [_ [Hnextarray [_ [_ [_ [Hnextedge _]]]]]].
  destruct Hnextarray as [Hnextlen Hnextbounds].
  assert (Hnextdefault : Znth last next 0 = Znth last next (-1)).
  { apply Znth_indep. rewrite Hnextlen. lia. }
  assert (Holdbound : 0 <= old < 26).
  { unfold old. rewrite Hnextdefault.
    specialize (Hnextbounds last Hlast). lia. }
  assert (Holdedge : Znth last next (-1) = old).
  { unfold old. symmetry. exact Hnextdefault. }
  assert (Hexisting0 :
    AdjacentInWords
      (sublist 0 z g ++
       cons (sublist 0 i (Znth z g (@nil Z))) (@nil (list Z)))
      (97 + last) (97 + old)).
  { apply (proj1 (Hnextedge last old Hlast Holdbound)). exact Holdedge. }
  pose proof (adjacent_processed_lift__word_failure_returns
    g z i (97 + last) (97 + old) Hz Hi Hexisting0) as Hexisting.
  pose proof (good_restoration_outgoing_unique__word_failure_returns
    g text (97 + last) (97 + old) (97 + cur)
    Hgood Hexisting Hcurrent) as Heq.
  unfold old in *. lia.
Qed.
Lemma incoming_conflict_no_restoration__word_failure_returns :
  forall g z i next prev used seen last cur,
    WordScanState g z i next prev used seen last ->
    0 <= z < Zlength g ->
    0 <= i <= Zlength (Znth z g (@nil Z)) ->
    0 <= last < 26 ->
    0 <= cur < 26 ->
    i < Zlength (Znth z g (@nil Z)) ->
    Znth i (Znth z g (@nil Z)) 0 = 97 + cur ->
    Znth cur prev 0 >= 0 ->
    Znth cur prev 0 <> last ->
    Spec g None.
Proof.
  intros g z i next prev used seen last cur Hstate Hz Hi Hlast Hcurbound
    Hilt Hcurvalue Hprevnonneg Hconflict.
  unfold Spec. intros text Hgood.
  unfold WordScanState in Hstate.
  destruct Hstate as [_ [Henc [_ [_ Hlaststate]]]].
  destruct Hlaststate as [[-> Hbad] | [Hipos Hlastvalue]]; [lia|].
  set (old := Znth cur prev 0).
  assert (Hlastchar : Znth (i - 1) (Znth z g (@nil Z)) 0 = 97 + last).
  { rewrite Hlastvalue. lia. }
  assert (Hwordin : In (Znth z g (@nil Z)) g).
  { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
  assert (Hcurrent : AdjacentInWords g (97 + last) (97 + cur)).
  { exists (Znth z g (@nil Z)), (i - 1).
    split; [exact Hwordin|].
    split; [lia|]. split; [lia|].
    split; [exact Hlastchar|].
    replace (i - 1 + 1) with i by lia. exact Hcurvalue. }
  pose proof Henc as Henc0.
  unfold EncodesGraph in Henc0.
  destruct Henc0 as [_ [_ [Hprevarray [_ [_ [_ Hprevedge]]]]]].
  destruct Hprevarray as [Hprevlen Hprevbounds].
  assert (Hprevdefault : Znth cur prev 0 = Znth cur prev (-1)).
  { apply Znth_indep. rewrite Hprevlen. lia. }
  change (Znth cur prev 0 >= 0) in Hprevnonneg.
  rewrite Hprevdefault in Hprevnonneg.
  assert (Holdbound : 0 <= old < 26).
  { unfold old. rewrite Hprevdefault.
    pose proof (Hprevbounds cur Hcurbound). lia. }
  assert (Holdedge : Znth cur prev (-1) = old).
  { unfold old. symmetry. exact Hprevdefault. }
  assert (Hexisting0 :
    AdjacentInWords
      (sublist 0 z g ++
       cons (sublist 0 i (Znth z g (@nil Z))) (@nil (list Z)))
      (97 + old) (97 + cur)).
  { apply (proj1 (Hprevedge old cur Holdbound Hcurbound)). exact Holdedge. }
  pose proof (adjacent_processed_lift__word_failure_returns
    g z i (97 + old) (97 + cur) Hz Hi Hexisting0) as Hexisting.
  pose proof (good_restoration_incoming_unique__word_failure_returns
    g text (97 + old) (97 + last) (97 + cur)
    Hgood Hexisting Hcurrent) as Heq.
  unfold old in *. lia.
Qed.
Lemma encoded_next_prev_zero_defaults__word_failure_returns :
  forall words next prev used from to,
    EncodesGraph words next prev used ->
    0 <= from < 26 ->
    0 <= to < 26 ->
    Znth from next 0 = to ->
    Znth to prev 0 = from.
Proof.
  intros words next prev used from to Henc Hfrom Hto Hnext0.
  unfold EncodesGraph in Henc.
  destruct Henc as [_ [Hnextarray [Hprevarray [_ [_ [Hnextedge Hprevedge]]]]]].
  destruct Hnextarray as [Hnextlen _].
  destruct Hprevarray as [Hprevlen _].
  assert (Hnextdefault : Znth from next 0 = Znth from next (-1)).
  { apply Znth_indep. rewrite Hnextlen. lia. }
  assert (Hnextminus : Znth from next (-1) = to).
  { rewrite <- Hnextdefault. exact Hnext0. }
  pose proof (proj1 (Hnextedge from to Hfrom Hto) Hnextminus) as Hadj.
  pose proof (proj2 (Hprevedge from to Hfrom Hto) Hadj) as Hprevminus.
  assert (Hprevdefault : Znth to prev 0 = Znth to prev (-1)).
  { apply Znth_indep. rewrite Hprevlen. lia. }
  rewrite Hprevdefault. exact Hprevminus.
Qed.
