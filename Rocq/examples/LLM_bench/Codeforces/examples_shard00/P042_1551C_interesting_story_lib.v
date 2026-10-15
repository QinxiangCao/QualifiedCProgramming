Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition InterestingWordSelection (words : list (list Z)) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength words) /\
  exists letter, 97 <= letter <= 101 /\
    2 * sum (fun i : Z => 0 <= i < Zlength words /\ chosen i) (fun i =>
      Zlength (filter (Z.eqb letter) (Znth i words nil))) >
    sum (fun i : Z => 0 <= i < Zlength words /\ chosen i)
      (fun i => Zlength (Znth i words nil)).
Definition Pre (words : list (list Z)) : Prop :=
  1 <= Zlength words <= 200000 /\ Forall (fun w => 0 < Zlength w /\
    Forall (fun c => 97 <= c <= 101) w) words.
Definition Spec (words : list (list Z)) (out : Z) : Prop :=
  (out = 0 /\ forall chosen, ~ InterestingWordSelection words chosen) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      InterestingWordSelection words (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength words /\ fst candidate i))
    snd out.

Require Import Coq.Sorting.Permutation.
From AUXLib Require ListLib.

(** The score used by the implementation for one word and one letter. *)
Definition LetterCount (letter : Z) (word : list Z) : Z :=
  Zlength (filter (Z.eqb letter) word).

Definition TotalLength (words : list (list Z)) : Z :=
  fold_right Z.add 0 (map (@Zlength Z) words).

Definition WordScore (letter : Z) (word : list Z) : Z :=
  2 * LetterCount letter word - Zlength word.

Definition ScoreBlock (words : list (list Z)) (letter : Z) : list Z :=
  map (WordScore letter) words.

Definition CountPrefixState
    (word : list Z) (scanned : Z) (counts : list Z) : Prop :=
  Zlength counts = 5 /\ 0 <= scanned <= Zlength word /\
  forall d, 0 <= d < 5 ->
    Znth d counts 0 = LetterCount (97 + d) (sublist 0 scanned word).

(** Memory contents while complete rows of the five score blocks are built. *)
Definition ScoreBuildState
    (words : list (list Z)) (done : Z) (mem : list (option Z)) : Prop :=
  Zlength mem = 5 * Zlength words /\
  forall d k,
    0 <= d < 5 -> 0 <= k < Zlength words ->
    (k < done ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (done <= k ->
       Znth (d * Zlength words + k) mem None = None).

(** The inner five-iteration loop has filled the first [letters] cells of row
    [row], in addition to every earlier row. *)
Definition ScoreRowState
    (words : list (list Z)) (row letters : Z)
    (mem : list (option Z)) : Prop :=
  Zlength mem = 5 * Zlength words /\
  forall d k,
    0 <= d < 5 -> 0 <= k < Zlength words ->
    (k < row ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (k = row /\ d < letters ->
       Znth (d * Zlength words + k) mem None =
       Some (WordScore (97 + d) (Znth k words nil))) /\
    (row < k \/ (k = row /\ letters <= d) ->
       Znth (d * Zlength words + k) mem None = None).

Definition ScoreTable (words : list (list Z)) (scores : list Z) : Prop :=
  Zlength scores = 5 * Zlength words /\
  forall d,
    0 <= d < 5 ->
    sublist (d * Zlength words) ((d + 1) * Zlength words) scores =
    ScoreBlock words (97 + d).

(** Blocks before [processed] have been sorted decreasingly; later blocks are
    still in their canonical word order. *)
Definition PreparedScoreTable
    (words : list (list Z)) (processed : Z) (scores : list Z) : Prop :=
  Zlength scores = 5 * Zlength words /\
  forall d,
    0 <= d < 5 ->
    let block := sublist (d * Zlength words)
                         ((d + 1) * Zlength words) scores in
    (d < processed ->
       Permutation (ScoreBlock words (97 + d)) block /\
       ListLib.decreasing block) /\
    (processed <= d -> block = ScoreBlock words (97 + d)).

Definition PositivePrefixState
    (block : list Z) (take acc : Z) : Prop :=
  0 <= take <= Zlength block /\
  acc = fold_right Z.add 0 (sublist 0 take block) /\
  forall k, 0 <= k < take ->
    0 < fold_right Z.add 0 (sublist 0 (k + 1) block).

Definition InterestingForLetter
    (words : list (list Z)) (letter : Z) (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength words) /\
  2 * sum (fun i : Z => 0 <= i < Zlength words /\ chosen i) (fun i =>
    LetterCount letter (Znth i words nil)) >
  sum (fun i : Z => 0 <= i < Zlength words /\ chosen i)
      (fun i => Zlength (Znth i words nil)).

Definition LetterBest
    (words : list (list Z)) (letter best : Z) : Prop :=
  (best = 0 /\ forall chosen, ~ InterestingForLetter words letter chosen) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      InterestingForLetter words letter (fst candidate) /\
      snd candidate = #(fun i : Z =>
        0 <= i < Zlength words /\ fst candidate i))
    snd best.

(** [answer] is the maximum optimum among letters already processed. *)
Definition AnswerState
    (words : list (list Z)) (processed answer : Z) : Prop :=
  0 <= processed <= 5 /\ 0 <= answer <= Zlength words /\
  (forall d, 0 <= d < processed ->
     exists best,
       LetterBest words (97 + d) best /\ best <= answer) /\
  (answer = 0 \/
   exists d, 0 <= d < processed /\ LetterBest words (97 + d) answer).

Require Import Coq.micromega.Lia.
Lemma total_length_nonneg__count_safety :
  forall words, 0 <= TotalLength words.
Proof.
  intros words.
  unfold TotalLength.
  induction words as [|word words IH]; cbn.
  - lia.
  - pose proof (Zlength_nonneg word).
    lia.
Qed.
Lemma word_length_le_total_length__count_safety :
  forall words i,
    0 <= i < Zlength words ->
    Zlength (Znth i words nil) <= TotalLength words.
Proof.
  induction words as [|word words IH]; intros i Hi.
  - rewrite Zlength_nil in Hi.
    lia.
  - rewrite Zlength_cons in Hi.
    change (Zlength (Znth i (word :: words) nil) <=
            Zlength word + TotalLength words).
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + cbn.
      pose proof (total_length_nonneg__count_safety words).
      lia.
    + rewrite Znth_cons by lia.
      specialize (IH (i - 1)).
      pose proof (Zlength_nonneg word).
      lia.
Qed.
Lemma letter_count_and_prefix_bounds__count_safety :
  forall words i scanned counts d,
    0 <= i < Zlength words ->
    0 <= d < 5 ->
    CountPrefixState (Znth i words nil) scanned counts ->
    0 <= Znth d counts 0 <= scanned /\
    Zlength (Znth i words nil) <= TotalLength words.
Proof.
  intros words i scanned counts d Hi Hd Hstate.
  destruct Hstate as [_ [Hscanned Hcounts]].
  split.
  - rewrite Hcounts by exact Hd.
    unfold LetterCount.
    split.
    + apply Zlength_nonneg.
    + assert (Hfilter :
          Zlength (filter (Z.eqb (97 + d)) (sublist 0 scanned (Znth i words nil))) <=
          Zlength (sublist 0 scanned (Znth i words nil))).
      { rewrite !Zlength_correct.
        apply Nat2Z.inj_le.
        apply filter_length_le. }
      rewrite Zlength_sublist in Hfilter by lia.
      lia.
  - apply word_length_le_total_length__count_safety.
    exact Hi.
Qed.
Lemma count_prefix_zero__char_prefix :
  forall word,
    CountPrefixState word 0 (repeat 0 (Z.to_nat 5)).
Proof.
  intros word.
  unfold CountPrefixState.
  split.
  - rewrite Zlength_correct, repeat_length.
    reflexivity.
  - split.
    + pose proof (Zlength_nonneg word).
      lia.
    + intros d Hd.
      rewrite Zsublist_nil by lia.
      unfold LetterCount.
      rewrite Zlength_nil.
      change (Znth d (@repeat Z 0 (Z.to_nat 5)) 0 = 0).
      apply Znth_repeat.
Qed.
Lemma count_prefix_step__char_prefix :
  forall word j counts digit,
    0 <= j < Zlength word ->
    0 <= digit < 5 ->
    Znth j word 0 = 97 + digit ->
    CountPrefixState word j counts ->
    CountPrefixState word (j + 1)
      (replace_Znth digit (Znth digit counts 0 + 1) counts).
Proof.
  intros word j counts digit Hj Hd Hchar Hstate.
  unfold CountPrefixState in Hstate |- *.
  destruct Hstate as [Hlength [Hscanned Hcount]].
  split.
  - rewrite ListLib.Zlength_replace_Znth.
    exact Hlength.
  - split.
    + lia.
    + intros d Hd'.
      rewrite (sublist_split 0 (j + 1) j word) by lia.
      rewrite (@sublist_single Z 0 j word) by lia.
      unfold LetterCount.
      rewrite filter_app, Zlength_app.
      specialize (Hcount d Hd').
      destruct (Z.eq_dec d digit) as [Heq | Hneq].
      * subst d.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Hchar.
        assert (Hsingleton :
            List.filter (Z.eqb (97 + digit)) (97 + digit :: nil) =
            (97 + digit :: nil)).
        { change ((if Z.eqb (97 + digit) (97 + digit)
                    then 97 + digit :: nil else nil) =
                  (97 + digit :: nil)).
          rewrite Z.eqb_refl.
          reflexivity. }
        rewrite Hsingleton, Zlength_cons, Zlength_nil.
        unfold LetterCount in Hcount.
        lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        rewrite Hchar.
        assert (Hsingleton :
            List.filter (Z.eqb (97 + d)) (97 + digit :: nil) = nil).
        { change ((if Z.eqb (97 + d) (97 + digit)
                    then 97 + digit :: nil else nil) = nil).
          assert (Heqb : Z.eqb (97 + d) (97 + digit) = false).
          { apply Z.eqb_neq. lia. }
          rewrite Heqb.
          reflexivity. }
        rewrite Hsingleton, Zlength_nil.
        unfold LetterCount in Hcount.
        lia.
Qed.
Lemma score_row_store_step__score_row :
  forall (words : list (list Z)) (i c : Z) (mem : list (option Z))
         (counts : list Z) (len : Z),
    0 <= i < Zlength words ->
    0 <= c < 5 ->
    len = Zlength (Znth i words nil) ->
    ScoreRowState words i c mem ->
    CountPrefixState (Znth i words nil) len counts ->
    ScoreRowState words i (c + 1)
      (replace_Znth (c * Zlength words + i)
        (Some (2 * Znth c counts 0 - len)) mem).
Proof.
  intros words i c mem counts len Hi Hc Hlen Hrow Hcount.
  unfold ScoreRowState in Hrow |- *.
  destruct Hrow as [Hmem Hcells].
  unfold CountPrefixState in Hcount.
  destruct Hcount as [_ [_ Hcounts]].
  assert (Hstored :
    2 * Znth c counts 0 - len =
    WordScore (97 + c) (Znth i words nil)).
  {
    specialize (Hcounts c Hc).
    rewrite (sublist_self (Znth i words nil) len Hlen) in Hcounts.
    unfold WordScore.
    rewrite Hcounts, Hlen.
    reflexivity.
  }
  split.
  - rewrite AUXLib.ListLib.Zlength_replace_Znth. exact Hmem.
  - intros d k Hd Hk.
    specialize (Hcells d k Hd Hk).
    assert (Htarget :
      0 <= c * Zlength words + i < Zlength mem) by
      (rewrite Hmem; nia).
    assert (Hcell :
      0 <= d * Zlength words + k < Zlength mem) by
      (rewrite Hmem; nia).
    assert (Hflat_inj : forall d' k',
      0 <= d' < 5 -> 0 <= k' < Zlength words ->
      c * Zlength words + i = d' * Zlength words + k' ->
      c = d' /\ i = k').
    {
      intros d' k' Hd' Hk' Heq.
      destruct (Z.lt_trichotomy c d') as [Hlt | [He | Hgt]].
      - exfalso. nia.
      - subst d'. split; [reflexivity | lia].
      - exfalso. nia.
    }
    destruct Hcells as [Hbefore [Hcurrent Hafter]].
    split.
    + intro Hki.
      assert (Hneq :
        c * Zlength words + i <> d * Zlength words + k).
      {
        intro Heq.
        destruct (Hflat_inj d k Hd Hk Heq) as [_ Hik].
        lia.
      }
      rewrite Znth_replace_Znth_Diff by assumption.
      apply Hbefore. exact Hki.
    + split.
      * intros [Hki Hdnext]. subst k.
        destruct (Z.eq_dec d c) as [-> | Hdc].
        -- rewrite Znth_replace_Znth_Same by exact Htarget.
           now rewrite Hstored.
        -- assert (Hneq :
             c * Zlength words + i <> d * Zlength words + i).
           {
             intro Heq.
             destruct (Hflat_inj d i Hd Hi Heq) as [Hcd _].
             apply Hdc. symmetry. exact Hcd.
           }
           rewrite Znth_replace_Znth_Diff by assumption.
           apply Hcurrent. split; [reflexivity | lia].
      * intro Hlater.
        assert (Hneq :
          c * Zlength words + i <> d * Zlength words + k).
        {
          intro Heq.
          destruct (Hflat_inj d k Hd Hk Heq) as [Hcd Hik].
          destruct Hlater as [Hik' | [Hki Hcd']]; lia.
        }
        rewrite Znth_replace_Znth_Diff by assumption.
        apply Hafter.
        destruct Hlater as [Hik | [Hki Hcd]]; [left | right]; lia.
Qed.
Lemma score_row_complete__score_row :
  forall (words : list (list Z)) (i : Z) (mem : list (option Z)),
    0 <= i < Zlength words ->
    ScoreRowState words i 5 mem ->
    ScoreBuildState words (i + 1) mem.
Proof.
  intros words i mem Hi Hrow.
  unfold ScoreRowState in Hrow.
  unfold ScoreBuildState.
  destruct Hrow as [Hmem Hcells].
  split; [exact Hmem |].
  intros d k Hd Hk.
  specialize (Hcells d k Hd Hk).
  destruct Hcells as [Hbefore [Hcurrent Hafter]].
  split.
  - intro Hdone.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + apply Hbefore. exact Hki.
    + apply Hcurrent. split; lia.
  - intro Hlater.
    apply Hafter. left. lia.
Qed.
Lemma Znth_map__score_table :
  forall (A B : Type) (f : A -> B) (xs : list A) (i : Z) (d : A),
    Znth i (map f xs) (f d) = f (Znth i xs d).
Proof.
  intros. unfold Znth. apply map_nth.
Qed.
Lemma Znth_map_inbounds__score_table :
  forall (A B : Type) (f : A -> B) (xs : list A)
      (i : Z) (da : A) (db : B),
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs i da db Hi. unfold Znth.
  apply ListLib.map_nth_len. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Zlength_map__score_table :
  forall (A B : Type) (f : A -> B) (xs : list A),
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs. induction xs as [|x xs IH].
  - rewrite Zlength_nil. reflexivity.
  - simpl. rewrite !Zlength_cons. lia.
Qed.
Lemma total_length_nonnegative__score_table :
  forall words, 0 <= TotalLength words.
Proof.
  induction words as [|word words IH].
  - unfold TotalLength. simpl. lia.
  - change (0 <= Zlength word + TotalLength words).
    pose proof (Zlength_nonneg word). lia.
Qed.
Lemma word_length_le_total__score_table :
  forall words k,
    0 <= k < Zlength words ->
    Zlength (Znth k words nil) <= TotalLength words.
Proof.
  induction words as [|word words IH]; intros k Hk.
  - rewrite Zlength_nil in Hk. lia.
  - rewrite Zlength_cons in Hk.
    change (TotalLength (word :: words)) with
      (Zlength word + TotalLength words).
    destruct (Z.eq_dec k 0) as [->|Hne].
    + rewrite Znth0_cons.
      pose proof (total_length_nonnegative__score_table words). lia.
    + assert (0 < k) by lia.
      rewrite Znth_cons by lia.
      specialize (IH (k - 1) ltac:(lia)).
      pose proof (Zlength_nonneg word). lia.
Qed.
Lemma word_score_abs_bound__score_table :
  forall letter word,
    - Zlength word <= WordScore letter word <= Zlength word.
Proof.
  intros letter word.
  unfold WordScore, LetterCount.
  pose proof (filter_length_le (Z.eqb letter) word) as Hfilter.
  assert (0 <= Zlength (filter (Z.eqb letter) word))
    by apply Zlength_nonneg.
  rewrite !Zlength_correct in *.
  lia.
Qed.
Lemma all_some_materialize__score_table :
  forall mem : list (option Z),
    (forall i, 0 <= i < Zlength mem ->
       exists z, Znth i mem None = Some z) ->
    exists values, mem = map Some values.
Proof.
  induction mem as [|entry mem IH]; intros Hall.
  - exists nil. reflexivity.
  - assert (Hhead : exists z, entry = Some z).
    {
      specialize (Hall 0).
      rewrite Zlength_cons in Hall.
      pose proof (Zlength_nonneg mem).
      specialize (Hall ltac:(lia)).
      rewrite Znth0_cons in Hall. exact Hall.
    }
    destruct Hhead as [z Hz]. subst entry.
    assert (Htail : forall i, 0 <= i < Zlength mem ->
      exists z0, Znth i mem None = Some z0).
    {
      intros i Hi. specialize (Hall (i + 1)).
      rewrite Zlength_cons in Hall.
      specialize (Hall ltac:(lia)).
      rewrite Znth_cons in Hall by lia.
      replace (i + 1 - 1) with i in Hall by lia.
      exact Hall.
    }
    destruct (IH Htail) as [values Hvalues]. subst mem.
    exists (z :: values). reflexivity.
Qed.
Lemma score_build_materialize__score_table :
  forall words mem,
    0 < Zlength words ->
    ScoreBuildState words (Zlength words) mem ->
    exists scores,
      mem = map Some scores /\ ScoreTable words scores.
Proof.
  intros words mem Hwords Hstate.
  destruct Hstate as [Hmem Hcells].
  assert (Hall : forall p, 0 <= p < Zlength mem ->
    exists z, Znth p mem None = Some z).
  {
    intros p Hp.
    set (n := Zlength words) in *.
    set (d := p / n).
    set (k := p mod n).
    assert (Hk : 0 <= k < n).
    { subst k. apply Z.mod_pos_bound. exact Hwords. }
    assert (Hd0 : 0 <= d).
    { subst d. apply Z_div_pos; lia. }
    assert (Hdeq : d * n + k = p).
    {
      subst d k. pose proof (Z.div_mod p n ltac:(lia)). nia.
    }
    assert (Hd5 : d < 5) by nia.
    specialize (Hcells d k ltac:(lia) ltac:(lia)).
    destruct Hcells as [Hfilled _].
    specialize (Hfilled ltac:(lia)).
    exists (WordScore (97 + d) (Znth k words nil)).
    rewrite Hdeq in Hfilled. exact Hfilled.
  }
  destruct (all_some_materialize__score_table mem Hall)
    as [scores Hscores].
  assert (Hscores_len : Zlength scores = 5 * Zlength words).
  {
    rewrite Hscores, Zlength_map__score_table in Hmem. exact Hmem.
  }
  exists scores. split; [exact Hscores|].
  unfold ScoreTable. split.
  - exact Hscores_len.
  - intros d Hd.
    apply (proj2 (list_eq_ext
      (sublist (d * Zlength words) ((d + 1) * Zlength words) scores)
      (ScoreBlock words (97 + d)) 0)).
    split.
    + unfold ScoreBlock.
      rewrite Zlength_sublist by nia.
      rewrite Zlength_map__score_table. lia.
    + intros k Hk.
      unfold ScoreBlock in *.
      rewrite Zlength_sublist in Hk by nia.
      rewrite Znth_sublist by nia.
      rewrite (Znth_map_inbounds__score_table
        (list Z) Z (WordScore (97 + d)) words k nil 0 ltac:(nia)).
      specialize (Hcells d k Hd ltac:(lia)).
      destruct Hcells as [Hfilled _].
      specialize (Hfilled ltac:(lia)).
      rewrite Hscores in Hfilled.
      rewrite (Znth_map_inbounds__score_table
        Z (option Z) (@Some Z) scores
        (d * Zlength words + k) 0 None ltac:(nia)) in Hfilled.
      injection Hfilled. intros Heq.
      replace (k + d * Zlength words) with
        (d * Zlength words + k) by lia.
      exact Heq.
Qed.
Lemma score_table_entry__score_table :
  forall words scores d k,
    ScoreTable words scores ->
    0 <= d < 5 ->
    0 <= k < Zlength words ->
    Znth (d * Zlength words + k) scores 0 =
      WordScore (97 + d) (Znth k words nil).
Proof.
  intros words scores d k Htable Hd Hk.
  destruct Htable as [Hlen Hblocks].
  specialize (Hblocks d Hd).
  apply (f_equal (fun xs => Znth k xs 0)) in Hblocks.
  rewrite Znth_sublist in Hblocks by nia.
  unfold ScoreBlock in Hblocks.
  rewrite (Znth_map_inbounds__score_table
    (list Z) Z (WordScore (97 + d)) words k nil 0 Hk) in Hblocks.
  replace (k + d * Zlength words) with
    (d * Zlength words + k) in Hblocks by lia.
  exact Hblocks.
Qed.
Lemma permutation_preserves_pointwise_bounds__block_sorting :
  forall (xs ys : list Z) lo hi,
    Permutation xs ys ->
    (forall i, 0 <= i < Zlength xs ->
       lo <= Znth i xs 0 <= hi) ->
    forall i, 0 <= i < Zlength ys ->
      lo <= Znth i ys 0 <= hi.
Proof.
  intros xs ys lo hi Hperm Hbounds.
  assert (Hxs : Forall (fun x => lo <= x <= hi) xs).
  { apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 xs)).
    exact Hbounds. }
  assert (Hys : Forall (fun x => lo <= x <= hi) ys).
  { eapply Permutation_Forall; eauto. }
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 ys) Hys).
Qed.
Lemma total_length_nonnegative__block_sorting :
  forall words, 0 <= TotalLength words.
Proof.
  induction words as [| word words IH].
  - reflexivity.
  - change (0 <= Zlength word + TotalLength words).
    pose proof (Zlength_nonneg word). lia.
Qed.
Lemma filter_zlength_le__block_sorting :
  forall (f : Z -> bool) xs,
    Zlength (filter f xs) <= Zlength xs.
Proof.
  intros f xs. induction xs as [| x xs IH].
  - reflexivity.
  - simpl. destruct (f x); rewrite ?Zlength_cons; lia.
Qed.
Lemma score_block_bounds__block_sorting :
  forall words letter,
    TotalLength words <= 200000 ->
    Forall (fun x => -200000 <= x <= 200000) (ScoreBlock words letter).
Proof.
  intros words. induction words as [| word words IH]; intros letter Htotal.
  - constructor.
  - simpl. constructor.
    + unfold WordScore, LetterCount.
      pose proof (Zlength_nonneg (filter (Z.eqb letter) word)) as Hcount0.
      pose proof (filter_zlength_le__block_sorting (Z.eqb letter) word)
        as Hcountle.
      pose proof (total_length_nonnegative__block_sorting words) as Htail0.
      change (Zlength word + TotalLength words <= 200000) in Htotal.
      lia.
    + apply IH.
      pose proof (Zlength_nonneg word).
      change (Zlength word + TotalLength words <= 200000) in Htotal.
      lia.
Qed.
Lemma prepared_table_pointwise_bounds__block_sorting :
  forall words processed scores,
    0 < Zlength words ->
    0 <= processed <= 5 ->
    TotalLength words <= 200000 ->
    PreparedScoreTable words processed scores ->
    forall p, 0 <= p < Zlength scores ->
      -200000 <= Znth p scores 0 <= 200000.
Proof.
  intros words processed scores Hwords Hprocessed Htotal Hprepared p Hp.
  unfold PreparedScoreTable in Hprepared.
  destruct Hprepared as [Hscores Hblocks].
  assert (Hblock_bounds : forall d,
      0 <= d < 5 ->
      Forall (fun x => -200000 <= x <= 200000)
        (sublist (d * Zlength words) ((d + 1) * Zlength words) scores)).
  { intros d Hd.
    specialize (Hblocks d Hd). cbn in Hblocks.
    destruct (Z_lt_ge_dec d processed) as [Hdlt | Hdge].
    - destruct Hblocks as [Hdone _]. specialize (Hdone Hdlt).
      destruct Hdone as [Hperm _].
      eapply Permutation_Forall.
      + exact Hperm.
      + apply score_block_bounds__block_sorting. exact Htotal.
    - destruct Hblocks as [_ Hcanonical].
      rewrite Hcanonical by lia.
      apply score_block_bounds__block_sorting. exact Htotal. }
  assert (Hpick : forall d,
      0 <= d < 5 ->
      d * Zlength words <= p < (d + 1) * Zlength words ->
      -200000 <= Znth p scores 0 <= 200000).
  { intros d Hd Hpd.
    pose proof (Hblock_bounds d Hd) as Hb.
    pose proof (proj1
      (Forall_Znth (fun x => -200000 <= x <= 200000) 0
        (sublist (d * Zlength words) ((d + 1) * Zlength words) scores))
      Hb (p - d * Zlength words)) as Hnth.
    specialize (Hnth ltac:(rewrite Zlength_sublist by nia; nia)).
    rewrite Znth_sublist in Hnth by nia.
    replace (p - d * Zlength words + d * Zlength words) with p in Hnth
      by nia.
    exact Hnth. }
  rewrite Hscores in Hp.
  destruct (Z_lt_ge_dec p (1 * Zlength words)) as [Hp0 | Hp0].
  - apply (Hpick 0); nia.
  - destruct (Z_lt_ge_dec p (2 * Zlength words)) as [Hp1 | Hp1].
    + apply (Hpick 1); nia.
    + destruct (Z_lt_ge_dec p (3 * Zlength words)) as [Hp2 | Hp2].
      * apply (Hpick 2); nia.
      * destruct (Z_lt_ge_dec p (4 * Zlength words)) as [Hp3 | Hp3].
        -- apply (Hpick 3); nia.
        -- apply (Hpick 4); nia.
Qed.
Lemma prepared_table_replace_block__block_sorting :
  forall words c n before block sorted after,
    n = Zlength words ->
    0 <= c < 5 ->
    Zlength before = c * n ->
    Zlength block = n ->
    Zlength sorted = n ->
    Zlength after = (5 - c - 1) * n ->
    PreparedScoreTable words c (before ++ block ++ after) ->
    Permutation block sorted ->
    ListLib.decreasing sorted ->
    PreparedScoreTable words (c + 1) (before ++ sorted ++ after) /\
    sublist (c * n) ((c + 1) * n)
      (before ++ sorted ++ after) = sorted.
Proof.
  intros words c n before block sorted after Hn Hc Hbefore Hblock
    Hsorted Hafter Hprepared Hperm Hdec.
  pose proof (Zlength_nonneg words) as Hnnonneg.
  unfold PreparedScoreTable in Hprepared |- *.
  destruct Hprepared as [Htotal Hblocks].
  assert (Hmiddle_old :
      sublist (c * n) ((c + 1) * n) (before ++ block ++ after) = block).
  { rewrite sublist_split_app_r with (len := c * n) by lia.
    replace (c * n - c * n) with 0 by lia.
    replace ((c + 1) * n - c * n) with n by lia.
    rewrite <- Hblock.
    apply sublist_app_exact1. }
  assert (Hmiddle_new :
      sublist (c * n) ((c + 1) * n) (before ++ sorted ++ after) = sorted).
  { rewrite sublist_split_app_r with (len := c * n) by lia.
    replace (c * n - c * n) with 0 by lia.
    replace ((c + 1) * n - c * n) with n by lia.
    rewrite <- Hsorted.
    apply sublist_app_exact1. }
  split.
  - split.
    + repeat rewrite Zlength_app. lia.
    + intros d Hd. cbn.
      split.
      * intros Hdprocessed.
        destruct (Z_lt_ge_dec d c) as [Hdc | Hcd].
        -- specialize (Hblocks d Hd). cbn in Hblocks.
           destruct Hblocks as [Hdone _].
           specialize (Hdone Hdc).
           assert (Hold :
             sublist (d * Zlength words) ((d + 1) * Zlength words)
               (before ++ block ++ after) =
             sublist (d * Zlength words) ((d + 1) * Zlength words) before).
           { apply sublist_split_app_l.
             - lia.
             - rewrite Hbefore, Hn. nia. }
           assert (Hnew :
             sublist (d * Zlength words) ((d + 1) * Zlength words)
               (before ++ sorted ++ after) =
             sublist (d * Zlength words) ((d + 1) * Zlength words) before).
           { apply sublist_split_app_l.
             - lia.
             - rewrite Hbefore, Hn. nia. }
           rewrite Hnew, <- Hold. exact Hdone.
        -- assert (d = c) by lia. subst d.
           rewrite <- Hn.
           rewrite Hmiddle_new.
           split; [|exact Hdec].
           specialize (Hblocks c Hd). cbn in Hblocks.
           destruct Hblocks as [_ Hcanonical].
           specialize (Hcanonical ltac:(lia)).
           rewrite <- Hn in Hcanonical.
           rewrite Hmiddle_old in Hcanonical.
           rewrite <- Hcanonical. exact Hperm.
      * intros Hdunprocessed.
        specialize (Hblocks d Hd). cbn in Hblocks.
        destruct Hblocks as [_ Hcanonical].
        specialize (Hcanonical ltac:(lia)).
        assert (Hold :
          sublist (d * Zlength words) ((d + 1) * Zlength words)
            (before ++ block ++ after) =
          sublist (d * Zlength words - c * n - n)
            ((d + 1) * Zlength words - c * n - n) after).
        { rewrite sublist_split_app_r with (len := c * n) by nia.
          rewrite sublist_split_app_r with (len := n) by nia.
          reflexivity. }
        assert (Hnew :
          sublist (d * Zlength words) ((d + 1) * Zlength words)
            (before ++ sorted ++ after) =
          sublist (d * Zlength words - c * n - n)
            ((d + 1) * Zlength words - c * n - n) after).
        { rewrite sublist_split_app_r with (len := c * n) by nia.
          rewrite sublist_split_app_r with (len := n) by nia.
          reflexivity. }
        rewrite Hnew, <- Hold. exact Hcanonical.
  - exact Hmiddle_new.
Qed.
Lemma positive_prefix_zero__positive_prefix :
  forall block : list Z,
    PositivePrefixState block 0 0.
Proof.
  intros block.
  unfold PositivePrefixState, sublist.
  simpl.
  pose proof (Zlength_nonneg block).
  repeat split; try lia.
Qed.
Lemma sum_sublist_snoc__positive_prefix :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    fold_right Z.add 0 (sublist 0 (i + 1) xs) =
    fold_right Z.add 0 (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  change (ListLib.sum (sublist 0 i xs ++ (Znth i xs 0 :: nil)) =
          ListLib.sum (sublist 0 i xs) + Znth i xs 0).
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.
Lemma positive_prefix_step__positive_prefix :
  forall (block : list Z) take acc,
    PositivePrefixState block take acc ->
    0 <= take < Zlength block ->
    0 < acc + Znth take block 0 ->
    PositivePrefixState block (take + 1) (acc + Znth take block 0).
Proof.
  intros block take acc [Htake [Hacc Hprefix]] Hbound Hpositive.
  unfold PositivePrefixState.
  split; [lia|].
  split.
  - rewrite sum_sublist_snoc__positive_prefix by exact Hbound.
    lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k take) as [Hlt | Hge].
    + apply Hprefix. lia.
    + assert (k = take) by lia. subst k.
      rewrite sum_sublist_snoc__positive_prefix by exact Hbound.
      lia.
Qed.
Lemma sum_permutation__positive_prefix :
  forall xs ys : list Z,
    Permutation xs ys ->
    fold_right Z.add 0 xs = fold_right Z.add 0 ys.
Proof.
  intros xs ys Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma sum_firstn_le_positive_parts__positive_prefix :
  forall (xs : list Z) n,
    fold_right Z.add 0 (firstn n xs) <=
    fold_right Z.add 0 (map (Z.max 0) xs).
Proof.
  induction xs as [|x xs IH]; intros n.
  - destruct n; simpl; apply Z.le_refl.
  - destruct n as [|n].
    + simpl.
      specialize (IH 0%nat).
      simpl in IH.
      pose proof (Z.le_max_l 0 x).
      lia.
    + simpl.
      specialize (IH n).
      pose proof (Z.le_max_r 0 x).
      lia.
Qed.
Lemma word_score_positive_part_bound__positive_prefix :
  forall letter word,
    Z.max 0 (WordScore letter word) <= Zlength word.
Proof.
  intros letter word.
  unfold WordScore, LetterCount.
  assert (Hfilter : Zlength (filter (Z.eqb letter) word) <= Zlength word).
  {
    rewrite !Zlength_correct.
    apply Nat2Z.inj_le.
    apply filter_length_le.
  }
  pose proof (Zlength_nonneg word).
  destruct (Z_le_gt_dec 0
    (2 * Zlength (filter (Z.eqb letter) word) - Zlength word)).
  - rewrite Z.max_r by lia. lia.
  - rewrite Z.max_l by lia. lia.
Qed.
Lemma positive_word_scores_total_bound__positive_prefix :
  forall words letter,
    fold_right Z.add 0
      (map (Z.max 0) (ScoreBlock words letter)) <=
    TotalLength words.
Proof.
  induction words as [|word words IH]; intros letter; simpl.
  - apply Z.le_refl.
  - pose proof (word_score_positive_part_bound__positive_prefix letter word).
    specialize (IH letter).
    apply Z.add_le_mono; assumption.
Qed.
Lemma positive_word_scores_sum_bound__positive_prefix :
  forall words letter block take,
    Permutation (ScoreBlock words letter) block ->
    0 <= take <= Zlength block ->
    fold_right Z.add 0 (sublist 0 take block) <= TotalLength words.
Proof.
  intros words letter block take Hperm Htake.
  assert (Hprefix :
    fold_right Z.add 0 (sublist 0 take block) <=
    fold_right Z.add 0 (map (Z.max 0) block)).
  {
    unfold sublist.
    simpl.
    apply sum_firstn_le_positive_parts__positive_prefix.
  }
  assert (Hparts :
    fold_right Z.add 0 (map (Z.max 0) (ScoreBlock words letter)) =
    fold_right Z.add 0 (map (Z.max 0) block)).
  {
    apply sum_permutation__positive_prefix.
    apply Permutation_map.
    exact Hperm.
  }
  pose proof (positive_word_scores_total_bound__positive_prefix words letter).
  lia.
Qed.
Lemma Zlength_map__letter_optimality : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma filter_members_firstn__letter_optimality : forall {A : Type}
    (xs : list A) k,
  NoDup xs ->
  Permutation
    (filter (fun x => if prop_dec (In x (firstn k xs)) then true else false) xs)
    (firstn k xs).
Proof.
  intros A xs k Hnd. apply NoDup_Permutation.
  - apply NoDup_filter. exact Hnd.
  - apply (NoDup_app_remove_r (firstn k xs) (skipn k xs)).
    rewrite firstn_skipn. exact Hnd.
  - intros x. rewrite filter_In. split.
    + intros [_ Htest]. destruct (prop_dec (In x (firstn k xs))) as [Hin|Hnot];
        [exact Hin|discriminate].
    + intros Hin. split.
      * rewrite <- (firstn_skipn k xs). apply in_or_app. left. exact Hin.
      * destruct (prop_dec (In x (firstn k xs))) as [_|Hnot];
          [reflexivity|contradiction].
Qed.
Lemma Znth_map__letter_optimality : forall {A B : Type} (f : A -> B) xs
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
Lemma Zlength_Zrange_aux__letter_optimality : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__letter_optimality : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__letter_optimality. lia.
Qed.
Lemma Znth_Zrange_aux__letter_optimality : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__letter_optimality : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__letter_optimality by lia. lia.
Qed.
Lemma map_Znth_Zrange__letter_optimality : forall {A : Type} (xs : list A) d,
  map (fun i => Znth i xs d) (Zrange 0 (Zlength xs)) = xs.
Proof.
  intros A xs d. apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite Zlength_map__letter_optimality,
      Zlength_Zrange__letter_optimality by apply Zlength_nonneg.
    lia.
  - intros i Hi.
    assert (Hlen0 : 0 <= Zlength xs) by apply Zlength_nonneg.
    rewrite Zlength_map__letter_optimality,
      Zlength_Zrange__letter_optimality in Hi by lia.
    rewrite (@Znth_map__letter_optimality Z A
      (fun j => Znth j xs d) (Zrange 0 (Zlength xs)) 0 d i) by
      (rewrite Zlength_Zrange__letter_optimality by lia; exact Hi).
    rewrite (Znth_Zrange__letter_optimality 0 (Zlength xs) i) by lia.
    replace (0 + i) with i by lia. reflexivity.
Qed.
Lemma sum_permutation__letter_optimality : forall xs ys : list Z,
  Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; lia.
Qed.
Lemma firstn_shift_upper__letter_optimality : forall x xs n,
  Forall (fun y : Z => y <= x) xs ->
  (n < length xs)%nat ->
  ListLib.sum (firstn (S n) xs) <=
  x + ListLib.sum (firstn n xs).
Proof.
  intros x xs. induction xs as [|y ys IH]; intros n Hall Hn.
  - simpl in Hn. exfalso. exact (Nat.nlt_0_r n Hn).
  - inversion Hall as [|? ? Hy Hys]; subst. destruct n as [|n].
    + simpl. lia.
    + simpl in Hn. apply Nat.succ_lt_mono in Hn.
      simpl. specialize (IH n Hys Hn).
      replace (x + (y + ListLib.sum (firstn n ys))) with
        (y + (x + ListLib.sum (firstn n ys))) by ring.
      apply Z.add_le_mono_l. exact IH.
Qed.
Lemma decreasing_filter_sum_le_prefix__letter_optimality :
  forall {A : Type} (f : A -> Z) (test : A -> bool) xs,
    ListLib.decreasing (map f xs) ->
    ListLib.sum (map f (filter test xs)) <=
    ListLib.sum (firstn (length (filter test xs)) (map f xs)).
Proof.
  intros A f test xs. induction xs as [|x xs IH]; intros Hdec; simpl.
  - lia.
  - pose proof (proj2 (mono_noninc_iff_decreasing (f x :: map f xs)) Hdec)
      as Hmono.
    apply mono_noninc_cons in Hmono as [Hhead Htail].
    pose proof (proj1 (mono_noninc_iff_decreasing (map f xs)) Htail)
      as Hdec_tail.
    specialize (IH Hdec_tail).
    destruct (test x) eqn:Htest; simpl.
    + lia.
    + destruct (filter test xs) as [|y ys] eqn:Hfilter; simpl in *; [lia|].
      assert (Hlen : (length ys < length (map f xs))%nat).
      { rewrite length_map. change (S (length ys) <= length xs)%nat.
        replace (S (length ys)) with (length (filter test xs)) by
          (rewrite Hfilter; reflexivity).
        pose proof (filter_length test xs). lia. }
      pose proof (firstn_shift_upper__letter_optimality
        (f x) (map f xs) (length ys) Hhead Hlen) as Hshift.
      eapply Z.le_trans; [exact IH | exact Hshift].
Qed.
Lemma nth_nonpositive_of_prefix__letter_optimality : forall xs k,
  mono_noninc xs ->
  (k < length xs)%nat ->
  ListLib.sum (firstn (S k) xs) <= 0 ->
  nth k xs 0 <= 0.
Proof.
  intros xs. induction xs as [|x xs IH]; intros k Hmono Hk Hsum.
  - simpl in Hk. exfalso. exact (Nat.nlt_0_r k Hk).
  - apply mono_noninc_cons in Hmono as [Hhead Htail].
    destruct k as [|k].
  + simpl in *. lia.
  + simpl in Hk. apply Nat.succ_lt_mono in Hk.
    simpl in Hsum |- *.
    change (x + ListLib.sum (firstn (S k) xs) <= 0) in Hsum.
    destruct (Z_le_gt_dec (nth k xs 0) 0) as [Hle|Hgt]; [exact Hle|].
    assert (Hkx : nth k xs 0 <= x).
    { rewrite Forall_forall in Hhead. apply Hhead. apply nth_In. exact Hk. }
    assert (Htail_sum : ListLib.sum (firstn (S k) xs) <= 0) by lia.
    pose proof (IH k Htail Hk Htail_sum). lia.
Qed.
Lemma skipn_after_nth_le__letter_optimality : forall xs k,
  mono_noninc xs ->
  (k < length xs)%nat ->
  Forall (fun z : Z => z <= nth k xs 0) (skipn (S k) xs).
Proof.
  intros xs. induction xs as [|x xs IH]; intros k Hmono Hk.
  - simpl in Hk. exfalso. exact (Nat.nlt_0_r k Hk).
  - apply mono_noninc_cons in Hmono as [Hhead Htail].
    destruct k as [|k].
    + simpl. exact Hhead.
    + simpl in Hk. apply Nat.succ_lt_mono in Hk.
      simpl. apply IH; assumption.
Qed.
Lemma sum_nonpositive__letter_optimality : forall xs,
  Forall (fun z : Z => z <= 0) xs -> ListLib.sum xs <= 0.
Proof.
  intros xs Hall. induction Hall; simpl; lia.
Qed.
Lemma Forall_firstn__letter_optimality : forall {A : Type}
    (P : A -> Prop) n xs,
  Forall P xs -> Forall P (firstn n xs).
Proof.
  intros A P n. induction n as [|n IH]; intros xs Hall; simpl.
  - constructor.
  - destruct xs as [|x xs]; [constructor|].
    inversion Hall as [|? ? Hx Hxs]; subst. constructor; [exact Hx|].
    apply IH. exact Hxs.
Qed.
Lemma prefix_after_nonpositive__letter_optimality : forall xs k m,
  mono_noninc xs ->
  (k < length xs)%nat ->
  ListLib.sum (firstn (S k) xs) <= 0 ->
  (S k <= m <= length xs)%nat ->
  ListLib.sum (firstn m xs) <= 0.
Proof.
  intros xs k m Hmono Hk Hprefix Hm.
  pose proof (nth_nonpositive_of_prefix__letter_optimality
    xs k Hmono Hk Hprefix) as Hnth.
  pose proof (skipn_after_nth_le__letter_optimality xs k Hmono Hk) as Htail.
  assert (Htail0 : Forall (fun z : Z => z <= 0) (skipn (S k) xs)).
  { rewrite !Forall_forall in Htail |- *. intros z Hz.
    specialize (Htail z Hz). lia. }
  rewrite <- (firstn_skipn (S k) xs) at 1.
  rewrite firstn_app.
  rewrite firstn_all2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l by lia.
  rewrite ListLib.sum_app.
  pose proof (sum_nonpositive__letter_optimality
    (firstn (m - S k) (skipn (S k) xs))) as Hrest.
  pose proof (Forall_firstn__letter_optimality
    (fun z : Z => z <= 0) (m - S k) _ Htail0) as Htail_first.
  specialize (Hrest Htail_first).
  lia.
Qed.
Lemma filter_permutation__letter_optimality : forall {A : Type}
    (test : A -> bool) xs ys,
  Permutation xs ys -> Permutation (filter test xs) (filter test ys).
Proof.
  intros A test xs ys Hperm. induction Hperm; simpl.
  - constructor.
  - destruct (test x); simpl; [apply perm_skip|]; exact IHHperm.
  - destruct (test x), (test y); simpl;
      try apply perm_swap; try apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.
Lemma fold_sum_map__letter_optimality : forall {A : Type}
    (f : A -> Z) xs,
  fold_right (fun x acc => f x + acc) 0 xs = ListLib.sum (map f xs).
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma finite_sum_as_filter__letter_optimality : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i))
    (f : Z -> Z) order,
  Permutation (Zrange lo hi) order ->
  @sum Z (fun i : Z => lo <= i < hi /\ P i) F f =
  ListLib.sum (map f
    (filter (fun i => if prop_dec (P i) then true else false) order)).
Proof.
  intros lo hi P F f order Hperm.
  unfold SumLib.Sum.sum.
  rewrite fold_sum_map__letter_optimality.
  apply sum_permutation__letter_optimality.
  apply Permutation_map.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - apply NoDup_filter. eapply Permutation_NoDup; [exact Hperm|].
    apply NoDup_Zrange.
  - intros x. rewrite <- enum_ok, filter_In. split.
    + intros [Hrange HP]. split.
      * eapply Permutation_in; [exact Hperm|]. apply In_Zrange. exact Hrange.
      * destruct (prop_dec (P x)) as [_|Hnot]; [reflexivity|contradiction].
    + intros [Hin Htest]. split.
      * apply In_Zrange. eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
        exact Hin.
      * destruct (prop_dec (P x)) as [HP|Hnot]; [exact HP|discriminate].
Qed.
Lemma sum_ones_length__letter_optimality : forall {A : Type} (xs : list A),
  ListLib.sum (map (fun _ => 1) xs) = Zlength xs.
Proof.
  intros A xs. induction xs as [|x xs IH].
  - reflexivity.
  - rewrite Zlength_cons. change (1 + ListLib.sum (map (fun _ : A => 1) xs) =
      Zlength xs + 1). rewrite IH. apply Z.add_comm.
Qed.
Lemma set_card_as_filter_length__letter_optimality : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i)) order,
  Permutation (Zrange lo hi) order ->
  @set_card Z (fun i : Z => lo <= i < hi /\ P i) F =
  Zlength
    (filter (fun i => if prop_dec (P i) then true else false) order).
Proof.
  intros lo hi P F order Hperm. unfold set_card.
  rewrite (finite_sum_as_filter__letter_optimality lo hi P
    F (fun _ => 1) order Hperm).
  apply sum_ones_length__letter_optimality.
Qed.
Lemma interesting_for_letter_iff_positive_wordscore_sum__letter_optimality :
  forall words letter chosen,
  InterestingForLetter words letter chosen <->
  (forall i, chosen i -> 0 <= i < Zlength words) /\
  0 < sum (fun i : Z => 0 <= i < Zlength words /\ chosen i)
    (fun i => WordScore letter (Znth i words nil)).
Proof.
  intros words letter chosen. unfold InterestingForLetter, WordScore.
  split; intros [Hbounds Hscore]; split; [exact Hbounds| |exact Hbounds|].
  - rewrite sum_sub, sum_factor_l. lia.
  - rewrite sum_sub, sum_factor_l in Hscore. lia.
Qed.
Lemma Zlength_firstn_to_nat__letter_optimality : forall {A : Type}
    (xs : list A) k,
  0 <= k <= Zlength xs ->
  Zlength (firstn (Z.to_nat k) xs) = k.
Proof.
  intros A xs k Hk. rewrite !Zlength_correct, length_firstn.
  rewrite Nat.min_l.
  - apply Z2Nat.id. lia.
  - rewrite Zlength_correct in Hk.
    rewrite <- (Nat2Z.id (length xs)). apply Z2Nat.inj_le; lia.
Qed.
Lemma sum_firstn_succ__letter_optimality : forall xs k,
  (k < length xs)%nat ->
  ListLib.sum (firstn (S k) xs) =
  ListLib.sum (firstn k xs) + nth k xs 0.
Proof.
  intros xs. induction xs as [|x xs IH]; intros k Hk.
  - simpl in Hk. exfalso. exact (Nat.nlt_0_r k Hk).
  - destruct k as [|k].
    + simpl. lia.
    + simpl in Hk. apply Nat.succ_lt_mono in Hk.
      change (x + ListLib.sum (firstn (S k) xs) =
        x + ListLib.sum (firstn k xs) + nth k xs 0).
      rewrite IH by exact Hk. lia.
Qed.
Lemma sorted_index_order_is_letter_best__letter_optimality :
  forall words letter order take,
  Permutation (Zrange 0 (Zlength words)) order ->
  ListLib.decreasing
    (map (fun i => WordScore letter (Znth i words nil)) order) ->
  0 <= take <= Zlength words ->
  (take > 0 ->
    0 < ListLib.sum (firstn (Z.to_nat take)
      (map (fun i => WordScore letter (Znth i words nil)) order))) ->
  (take = Zlength words \/
    ListLib.sum (firstn (S (Z.to_nat take))
      (map (fun i => WordScore letter (Znth i words nil)) order)) <= 0) ->
  LetterBest words letter take.
Proof.
  intros words letter order take Hperm Hdec Htake Hpositive Hstop.
  set (f := fun i => WordScore letter (Znth i words nil)).
  assert (Hlen : Zlength order = Zlength words).
  { pose proof (Permutation_length Hperm) as Hplen.
    rewrite Zlength_correct, <- Hplen, <- Zlength_correct.
    rewrite Zlength_Zrange__letter_optimality by apply Zlength_nonneg. lia. }
  assert (Hnd : NoDup order).
  { eapply Permutation_NoDup; [exact Hperm|apply NoDup_Zrange]. }
  assert (Hmono : mono_noninc (map f order)).
  { apply (proj2 (mono_noninc_iff_decreasing (map f order))). exact Hdec. }
  assert (Hselected_bound : forall chosen,
    0 < sum (fun i : Z => 0 <= i < Zlength words /\ chosen i) f ->
    #(fun i : Z => 0 <= i < Zlength words /\ chosen i) <= take).
  { intros chosen Hselected_positive.
    set (selected := filter
      (fun i => if prop_dec (chosen i) then true else false) order).
    assert (Hsum : sum
        (fun i : Z => 0 <= i < Zlength words /\ chosen i) f =
        ListLib.sum (map f selected)).
    { subst selected. apply finite_sum_as_filter__letter_optimality. exact Hperm. }
    assert (Hcard : #(fun i : Z =>
        0 <= i < Zlength words /\ chosen i) = Zlength selected).
    { subst selected. apply set_card_as_filter_length__letter_optimality.
      exact Hperm. }
    destruct Hstop as [Hexhausted|Hnext].
    - rewrite Hcard, Hexhausted, <- Hlen.
      rewrite !Zlength_correct. apply Nat2Z.inj_le. subst selected.
      pose proof (filter_length
        (fun i => if prop_dec (chosen i) then true else false) order) as Hfl.
      rewrite <- Hfl. apply Nat.le_add_r.
    - destruct (Z_le_gt_dec (Zlength selected) take) as [Hle|Hgt];
        [rewrite Hcard; exact Hle|].
      assert (Hsellen : Zlength selected <= Zlength order).
      { rewrite !Zlength_correct. apply Nat2Z.inj_le. subst selected.
        pose proof (filter_length
          (fun i => if prop_dec (chosen i) then true else false) order) as Hfl.
        rewrite <- Hfl. apply Nat.le_add_r. }
      assert (Htake_lt : take < Zlength words) by lia.
      assert (Hordernat : (Z.to_nat take < length (map f order))%nat).
      { rewrite length_map. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia. rewrite <- Zlength_correct, Hlen. exact Htake_lt. }
      assert (Hmrange :
          (S (Z.to_nat take) <= length selected <= length (map f order))%nat).
      { rewrite length_map. split.
        - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
          rewrite <- Zlength_correct. lia.
        - subst selected. pose proof (filter_length
            (fun i => if prop_dec (chosen i) then true else false) order) as Hfl.
          rewrite <- Hfl. apply Nat.le_add_r. }
      pose proof (decreasing_filter_sum_le_prefix__letter_optimality
        f (fun i => if prop_dec (chosen i) then true else false)
        order Hdec) as Htop.
      fold selected in Htop.
      pose proof (prefix_after_nonpositive__letter_optimality
        (map f order) (Z.to_nat take) (length selected)
        Hmono Hordernat Hnext Hmrange) as Hnonpos.
      rewrite Hsum in Hselected_positive. lia.
  }
  unfold LetterBest. destruct (Z.eq_dec take 0) as [Hzero|Hnonzero].
  - left. split; [exact Hzero|]. intros chosen Hinteresting.
    apply interesting_for_letter_iff_positive_wordscore_sum__letter_optimality
      in Hinteresting as [_ Hscore].
    specialize (Hselected_bound chosen Hscore). rewrite Hzero in Hselected_bound.
    set (selected := filter
      (fun i => if prop_dec (chosen i) then true else false) order).
    assert (Hsum : sum
        (fun i : Z => 0 <= i < Zlength words /\ chosen i) f =
        ListLib.sum (map f selected)).
    { subst selected. apply finite_sum_as_filter__letter_optimality. exact Hperm. }
    assert (Hcard : #(fun i : Z =>
        0 <= i < Zlength words /\ chosen i) = Zlength selected).
    { subst selected. apply set_card_as_filter_length__letter_optimality.
      exact Hperm. }
    rewrite Hcard in Hselected_bound.
    assert (selected = nil).
    { apply Zlength_nil_inv. pose proof (Zlength_nonneg selected). lia. }
    fold f in Hscore.
    rewrite Hsum, H in Hscore. simpl in Hscore. lia.
  - right. unfold max_value_of_subset, max_object_of_subset.
    set (chosen_prefix := fun i : Z => In i (firstn (Z.to_nat take) order)).
    exists (chosen_prefix, take). split.
    + split.
      * split.
        -- apply interesting_for_letter_iff_positive_wordscore_sum__letter_optimality.
           split.
           ++ intros i Hi. subst chosen_prefix. cbn in Hi.
              assert (Hinorder : In i order).
              { rewrite <- (firstn_skipn (Z.to_nat take) order).
                apply in_or_app. left. exact Hi. }
              eapply Permutation_in in Hinorder; [|apply Permutation_sym; exact Hperm].
              apply In_Zrange in Hinorder. exact Hinorder.
           ++ assert (Htakepos : take > 0) by lia.
              specialize (Hpositive Htakepos).
              subst chosen_prefix.
              rewrite (finite_sum_as_filter__letter_optimality
                0 (Zlength words)
                (fun i => In i (firstn (Z.to_nat take) order))
                _ f order Hperm).
              pose proof (filter_members_firstn__letter_optimality
                order (Z.to_nat take) Hnd) as Hfp.
              pose proof (Permutation_map f Hfp) as Hfpm.
              rewrite (sum_permutation__letter_optimality _ _ Hfpm).
              rewrite <- firstn_map. fold f in Hpositive. exact Hpositive.
        -- change (take = #(fun i : Z => 0 <= i < Zlength words /\
             chosen_prefix i)). unfold chosen_prefix.
           assert (Hcardprefix : #(fun i : Z => 0 <= i < Zlength words /\
               In i (firstn (Z.to_nat take) order)) =
             Zlength (filter (fun i => if prop_dec
               (In i (firstn (Z.to_nat take) order)) then true else false)
               order)).
           { apply set_card_as_filter_length__letter_optimality. exact Hperm. }
           rewrite Hcardprefix.
           pose proof (filter_members_firstn__letter_optimality
             order (Z.to_nat take) Hnd) as Hfp.
           rewrite Zlength_correct, (Permutation_length Hfp), <- Zlength_correct.
           symmetry. apply Zlength_firstn_to_nat__letter_optimality. lia.
      * intros [chosen amount] Hcandidate.
        change (InterestingForLetter words letter chosen /\
          amount = #(fun i : Z => 0 <= i < Zlength words /\ chosen i))
          in Hcandidate.
        change (amount <= take). destruct Hcandidate as [Hinteresting Hamount].
        apply interesting_for_letter_iff_positive_wordscore_sum__letter_optimality
          in Hinteresting as [_ Hscore].
        rewrite Hamount. exact (Hselected_bound chosen Hscore).
    + reflexivity.
Qed.
Lemma decreasing_positive_prefix_is_letter_best__letter_optimality :
  forall words letter block take acc,
  Permutation (ScoreBlock words letter) block ->
  ListLib.decreasing block ->
  PositivePrefixState block take acc ->
  (take = Zlength block \/
    (take < Zlength block /\ acc + Znth take block 0 <= 0)) ->
  LetterBest words letter take.
Proof.
  intros words letter block take acc Hblockperm Hblockdec Hstate Hterminal.
  set (f := fun i => WordScore letter (Znth i words nil)).
  assert (Hblocklen : Zlength block = Zlength words).
  { pose proof (Permutation_length Hblockperm) as Hplen.
    rewrite !Zlength_correct, <- Hplen. unfold ScoreBlock.
    rewrite length_map. reflexivity. }
  assert (Hcanonical : ScoreBlock words letter =
      map f (Zrange 0 (Zlength words))).
  { unfold ScoreBlock. rewrite <- (map_Znth_Zrange__letter_optimality words nil)
      at 1. rewrite map_map. unfold f. reflexivity. }
  assert (Hbm : Permutation block (map f (Zrange 0 (Zlength words)))).
  { rewrite <- Hcanonical. apply Permutation_sym. exact Hblockperm. }
  destruct (Permutation_map_inv f (Zrange 0 (Zlength words)) Hbm)
    as [order [Hblockeq Horder]].
  destruct Hstate as [[Htake0 Htakele] [Hacc Hprefix]].
  eapply sorted_index_order_is_letter_best__letter_optimality
    with (order := order).
  - exact Horder.
  - fold f. rewrite <- Hblockeq. exact Hblockdec.
  - rewrite <- Hblocklen. split; assumption.
  - intros Htakepos. fold f. rewrite <- Hblockeq.
    specialize (Hprefix (take - 1) ltac:(lia)).
    replace (take - 1 + 1) with take in Hprefix by lia.
    unfold sublist in Hprefix. simpl in Hprefix. exact Hprefix.
  - destruct Hterminal as [Hexhausted|[Hnotend Hnext]].
    + left. lia.
    + right. fold f. rewrite <- Hblockeq.
      assert (Hknat : (Z.to_nat take < length block)%nat).
      { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct. exact Hnotend. }
      rewrite sum_firstn_succ__letter_optimality by
        exact Hknat.
      change (acc = ListLib.sum (firstn (Z.to_nat take) block)) in Hacc.
      rewrite <- Hacc. unfold Znth in Hnext. exact Hnext.
Qed.
Lemma total_length_nonneg__answer_transition :
  forall words : list (list Z), 0 <= TotalLength words.
Proof.
  induction words as [| head tail IH].
  - reflexivity.
  - unfold TotalLength in *. simpl.
    pose proof (Zlength_nonneg head). lia.
Qed.
Lemma member_length_le_total__answer_transition :
  forall (words : list (list Z)) (word : list Z),
    In word words -> Zlength word <= TotalLength words.
Proof.
  induction words as [| head tail IH]; intros word Hin.
  - inversion Hin.
  - simpl in Hin.
    change (Zlength word <= Zlength head + TotalLength tail).
    destruct Hin as [Heq | Hin].
    + subst head.
      pose proof (total_length_nonneg__answer_transition tail). lia.
    + specialize (IH word Hin).
      pose proof (Zlength_nonneg head). lia.
Qed.
Lemma word_score_bounds__answer_transition :
  forall (words : list (list Z)) (letter : Z) (word : list Z),
    In word words -> TotalLength words <= 200000 ->
    -200000 <= WordScore letter word <= 200000.
Proof.
  intros words letter word Hin Htotal.
  pose proof (member_length_le_total__answer_transition words word Hin) as Hword.
  assert (Hcount : 0 <= LetterCount letter word <= Zlength word).
  {
    unfold LetterCount. rewrite !Zlength_correct.
    pose proof (filter_length_le (Z.eqb letter) word).
    lia.
  }
  unfold WordScore. lia.
Qed.
Lemma score_block_bounds__answer_transition :
  forall (words : list (list Z)) (letter : Z),
    TotalLength words <= 200000 ->
    Forall (fun score => -200000 <= score <= 200000)
      (ScoreBlock words letter).
Proof.
  intros words letter Htotal.
  apply Forall_forall. intros score Hin.
  unfold ScoreBlock in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [word [Heq Hin]].
  subst score.
  exact (word_score_bounds__answer_transition words letter word Hin Htotal).
Qed.
Lemma prepared_score_entry_bound_in_block__answer_transition :
  forall (words : list (list Z)) (processed d k : Z) (scores : list Z),
    TotalLength words <= 200000 ->
    PreparedScoreTable words processed scores ->
    0 <= d < 5 -> 0 <= k < Zlength words ->
    -200000 <= Znth (d * Zlength words + k) scores 0 <= 200000.
Proof.
  intros words processed d k scores Htotal Hprepared Hd Hk.
  unfold PreparedScoreTable in Hprepared.
  destruct Hprepared as [Hlength Hblocks].
  specialize (Hblocks d Hd).
  cbn in Hblocks.
  destruct Hblocks as [Hbefore Hafter].
  set (block := sublist (d * Zlength words)
                        ((d + 1) * Zlength words) scores).
  assert (Hbounded : Forall (fun value => -200000 <= value <= 200000) block).
  {
    destruct (Z_lt_ge_dec d processed) as [Hlt | Hge].
    - specialize (Hbefore Hlt). destruct Hbefore as [Hperm _].
      eapply Permutation_Forall; eauto using score_block_bounds__answer_transition.
    - specialize (Hafter ltac:(lia)).
      subst block. rewrite Hafter.
      apply score_block_bounds__answer_transition. exact Htotal.
  }
  rewrite Forall_forall in Hbounded.
  specialize (Hbounded (Znth k block 0)).
  assert (Hin : In (Znth k block 0) block).
  {
    unfold Znth. apply nth_In.
    rewrite <- (Nat2Z.id (length block)).
    rewrite <- Zlength_correct.
    apply (proj1 (Z2Nat.inj_lt k (Zlength block)
      ltac:(lia) ltac:(apply Zlength_nonneg))).
    subst block. rewrite Zlength_correct.
    rewrite sublist_length by nia.
    rewrite Z2Nat.id by nia. lia.
  }
  specialize (Hbounded Hin).
  subst block.
  rewrite Znth_sublist in Hbounded by nia.
  replace (k + d * Zlength words) with (d * Zlength words + k) in Hbounded by lia.
  exact Hbounded.
Qed.
Lemma prepared_score_entry_bounds__answer_transition :
  forall (words : list (list Z)) (processed p : Z) (scores : list Z),
    1 <= Zlength words -> TotalLength words <= 200000 ->
    PreparedScoreTable words processed scores ->
    0 <= p < 5 * Zlength words ->
    -200000 <= Znth p scores 0 <= 200000.
Proof.
  intros words processed p scores Hpositive Htotal Hprepared Hp.
  destruct (Z_lt_ge_dec p (Zlength words)) as [H0 | H0].
  - replace p with (0 * Zlength words + p) by lia.
    eapply prepared_score_entry_bound_in_block__answer_transition; eauto; lia.
  - destruct (Z_lt_ge_dec p (2 * Zlength words)) as [H1 | H1].
    + replace p with (1 * Zlength words + (p - Zlength words)) by lia.
      eapply prepared_score_entry_bound_in_block__answer_transition; eauto; lia.
    + destruct (Z_lt_ge_dec p (3 * Zlength words)) as [H2 | H2].
      * replace p with (2 * Zlength words + (p - 2 * Zlength words)) by lia.
        eapply prepared_score_entry_bound_in_block__answer_transition; eauto; lia.
      * destruct (Z_lt_ge_dec p (4 * Zlength words)) as [H3 | H3].
        -- replace p with (3 * Zlength words + (p - 3 * Zlength words)) by lia.
           eapply prepared_score_entry_bound_in_block__answer_transition; eauto; lia.
        -- replace p with (4 * Zlength words + (p - 4 * Zlength words)) by lia.
           eapply prepared_score_entry_bound_in_block__answer_transition; eauto; lia.
Qed.
Lemma answer_state_step__answer_transition :
  forall (words : list (list Z)) (processed answer best : Z),
    0 <= processed < 5 ->
    0 <= best <= Zlength words ->
    AnswerState words processed answer ->
    LetterBest words (97 + processed) best ->
    AnswerState words (processed + 1) (Z.max answer best).
Proof.
  intros words processed answer best Hprocessed Hbest Hstate Hcurrent.
  unfold AnswerState in Hstate |- *.
  destruct Hstate as [Hproc [Hanswer [Hprior Hrepresented]]].
  assert (Hmaxbounds : 0 <= Z.max answer best <= Zlength words).
  {
    destruct (Z.max_spec answer best) as [[Hle Heq] | [Hle Heq]];
      rewrite Heq; lia.
  }
  repeat split.
  - lia.
  - lia.
  - exact (proj1 Hmaxbounds).
  - exact (proj2 Hmaxbounds).
  - intros d Hd.
    destruct (Z_lt_ge_dec d processed) as [Hlt | Hge].
    + destruct (Hprior d ltac:(lia)) as [old_best [Hold Hbound]].
      exists old_best. split; [exact Hold |].
      eapply Z.le_trans; [exact Hbound | apply Z.le_max_l].
    + assert (d = processed) by lia. subst d.
      exists best. split; [exact Hcurrent | apply Z.le_max_r].
  - destruct (Z_le_gt_dec best answer) as [Hle | Hgt].
    + rewrite Z.max_l by exact Hle.
      destruct Hrepresented as [Hzero | [d [Hd Hold]]].
      * left. exact Hzero.
      * right. exists d. split; [lia | exact Hold].
    + rewrite Z.max_r by lia.
      right. exists processed. repeat split; try lia. exact Hcurrent.
Qed.
Lemma set_card_positive_of_member__final_result :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) (x : A),
    P x -> 0 < @set_card A P FP.
Proof.
  intros A P FP x Hx.
  assert (Hnonneg : 0 <= @set_card A P FP).
  {
    unfold set_card.
    apply SumLib.Sum.sum_nonneg.
    intros y Hy. lia.
  }
  assert (Hnonzero : @set_card A P FP <> 0).
  {
    intro Hzero.
    unfold set_card in Hzero.
    pose proof (@SumLib.Sum.sum_nonneg_eq_zero_elim
      A P FP (fun _ => 1)
      ltac:(intros y Hy; lia) Hzero x Hx) as Hone.
    lia.
  }
  lia.
Qed.
Lemma interesting_selection_extract_letter__final_result :
  forall words chosen,
    InterestingWordSelection words chosen ->
    exists d, 0 <= d < 5 /\
      InterestingForLetter words (97 + d) chosen.
Proof.
  intros words chosen Hinteresting.
  unfold InterestingWordSelection in Hinteresting.
  destruct Hinteresting as [Hbounds [letter [Hletter Hscore]]].
  exists (letter - 97).
  split; [lia |].
  unfold InterestingForLetter, LetterCount.
  replace (97 + (letter - 97)) with letter by lia.
  exact (conj Hbounds Hscore).
Qed.
Lemma interesting_for_letter_to_selection__final_result :
  forall words letter chosen,
    97 <= letter <= 101 ->
    InterestingForLetter words letter chosen ->
    InterestingWordSelection words chosen.
Proof.
  intros words letter chosen Hletter Hinteresting.
  unfold InterestingForLetter, LetterCount in Hinteresting.
  unfold InterestingWordSelection.
  destruct Hinteresting as [Hbounds Hscore].
  split; [exact Hbounds |].
  exists letter. exact (conj Hletter Hscore).
Qed.
Lemma interesting_for_letter_card_positive__final_result :
  forall words letter chosen,
    InterestingForLetter words letter chosen ->
    0 < #(fun i : Z =>
      0 <= i < Zlength words /\ chosen i).
Proof.
  intros words letter chosen Hinteresting.
  unfold InterestingForLetter in Hinteresting.
  destruct Hinteresting as [Hbounds Hscore].
  set (P := fun i : Z => 0 <= i < Zlength words /\ chosen i).
  assert (Hex : exists i, P i).
  {
    apply NNPP. intro Hnone.
    assert (Hempty : forall i, P i -> False).
    { intros i Hi. apply Hnone. exists i. exact Hi. }
    assert (Hletters :
      sum P (fun i => LetterCount letter (Znth i words nil)) = 0).
    {
      transitivity (sum P (fun _ => 0)).
      - apply SumLib.Sum.sum_ext. intros i Hi.
        exfalso. exact (Hempty i Hi).
      - apply SumLib.Sum.sum_zero.
    }
    assert (Hlengths :
      sum P (fun i => Zlength (Znth i words nil)) = 0).
    {
      transitivity (sum P (fun _ => 0)).
      - apply SumLib.Sum.sum_ext. intros i Hi.
        exfalso. exact (Hempty i Hi).
      - apply SumLib.Sum.sum_zero.
    }
    change (2 * sum P (fun i => LetterCount letter (Znth i words nil)) >
      sum P (fun i => Zlength (Znth i words nil))) in Hscore.
    rewrite Hletters, Hlengths in Hscore. lia.
  }
  destruct Hex as [i Hi].
  apply (@set_card_positive_of_member__final_result
    Z P _ i Hi).
Qed.
Lemma answer_state_five_implies_spec__final_result :
  forall words answer,
    AnswerState words 5 answer -> Spec words answer.
Proof.
  intros words answer Hstate.
  unfold AnswerState in Hstate.
  destruct Hstate as [Hprocessed [Hanswer [Hall Hattained]]].
  unfold Spec.
  destruct (Z.eq_dec answer 0) as [Hzero | Hnonzero].
  - left. split; [exact Hzero |].
    intros chosen Hselection.
    destruct (interesting_selection_extract_letter__final_result
      words chosen Hselection) as [d [Hd Hletter]].
    specialize (Hall d Hd) as [best [Hbest Hbest_le]].
    unfold LetterBest in Hbest.
    destruct Hbest as [[Hbest_zero Hnone] | Hmax].
    + exact (Hnone chosen Hletter).
    + unfold max_value_of_subset, max_object_of_subset in Hmax.
      destruct Hmax as [candidate [[Hcandidate Hupper] Hcandidate_value]].
      assert (Hcandidate_chosen :
        InterestingForLetter words (97 + d) chosen /\
        #(fun i : Z => 0 <= i < Zlength words /\ chosen i) =
        #(fun i : Z => 0 <= i < Zlength words /\ chosen i)).
      { split; [exact Hletter | reflexivity]. }
      specialize (Hupper
        (chosen, #(fun i : Z =>
          0 <= i < Zlength words /\ chosen i))
        Hcandidate_chosen).
      simpl in Hupper.
      pose proof (interesting_for_letter_card_positive__final_result
        words (97 + d) chosen Hletter) as Hpositive.
      rewrite Hcandidate_value in Hupper.
      lia.
  - right.
    destruct Hattained as [Hzero | [d [Hd Hbest_answer]]]; [contradiction |].
    unfold LetterBest in Hbest_answer.
    destruct Hbest_answer as [[Hzero Hnone] | Hmax]; [contradiction |].
    unfold max_value_of_subset, max_object_of_subset in Hmax.
    destruct Hmax as [candidate [[Hcandidate Hupper] Hcandidate_value]].
    exists candidate.
    split.
    + split.
      * destruct Hcandidate as [Hcandidate_letter Hcandidate_card].
        split.
        -- apply (interesting_for_letter_to_selection__final_result
             words (97 + d) (fst candidate)); [lia | exact Hcandidate_letter].
        -- exact Hcandidate_card.
      * intros competitor Hcompetitor.
        destruct Hcompetitor as [Hcompetitor_selection Hcompetitor_card].
        destruct (interesting_selection_extract_letter__final_result
          words (fst competitor) Hcompetitor_selection)
          as [d' [Hd' Hcompetitor_letter]].
        specialize (Hall d' Hd') as [best [Hbest Hbest_le]].
        unfold LetterBest in Hbest.
        destruct Hbest as [[Hbest_zero Hnone] | Hmax_best].
        -- exact (False_ind _ (Hnone (fst competitor) Hcompetitor_letter)).
        -- unfold max_value_of_subset, max_object_of_subset in Hmax_best.
           destruct Hmax_best as
             [best_candidate [[Hbest_candidate Hbest_upper] Hbest_value]].
           specialize (Hbest_upper competitor
             (conj Hcompetitor_letter Hcompetitor_card)).
           rewrite Hbest_value in Hbest_upper.
           rewrite Hcandidate_value.
           exact (Z.le_trans _ _ _ Hbest_upper Hbest_le).
    + exact Hcandidate_value.
Qed.
