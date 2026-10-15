Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition OneCandyTurn
    (m : Z) (before after : list (Z * Z)) : Prop :=
  exists child need rest,
    before = (child, need) :: rest /\
    ((need <= m /\ after = rest) \/
     (need > m /\ after = rest ++ [(child, need - m)])).

Definition CandyQueueTrace
    (m : Z) (initial : list (Z * Z)) (states : list (list (Z * Z))) : Prop :=
  2 <= Zlength states /\
  Znth 0 states [] = initial /\
  Znth (Zlength states - 1) states [] = [] /\
  forall k, 0 <= k < Zlength states - 1 ->
    OneCandyTurn m (Znth k states []) (Znth (k + 1) states []).

Definition Pre (m : Z) (wants : list Z) : Prop :=
  1 <= Zlength wants <= 100 /\
  1 <= m <= 100 /\
  Forall (fun need => 1 <= need <= 100) wants.

Definition Spec (m : Z) (wants : list Z) (out : Z) : Prop :=
  exists states need rest,
    CandyQueueTrace m (combine (Zrange 1 (Zlength wants + 1)) wants) states /\
    Znth (Zlength states - 2) states [] = (out, need) :: rest.

Definition CandyTurns (m need : Z) : Z :=
  (need + m - 1) / m.

Definition LastMaxPrefix
    (m : Z) (wants : list Z)
    (processed best answer : Z) : Prop :=
  0 <= processed <= Zlength wants /\
  ((processed = 0 /\ best = 0 /\ answer = 1) \/
   (0 < processed /\
    1 <= answer <= processed /\
    best = CandyTurns m (Znth (answer - 1) wants 0) /\
    (forall j, 0 <= j < processed ->
       CandyTurns m (Znth j wants 0) <= best) /\
    (forall j, answer <= j < processed ->
       CandyTurns m (Znth j wants 0) < best))).

Require Import Coq.micromega.Lia.
Lemma last_max_prefix_update_ge__prefix_updates :
  forall m wants i best answer current,
    0 <= i < Zlength wants ->
    LastMaxPrefix m wants i best answer ->
    current = CandyTurns m (Znth i wants 0) ->
    best <= current ->
    LastMaxPrefix m wants (i + 1) current (i + 1).
Proof.
  intros m wants i best answer current Hi Hprefix Hcurrent Hge.
  unfold LastMaxPrefix in *.
  destruct Hprefix as [Hbounds [Hzero | Hpositive]].
  - destruct Hzero as [Hi0 [Hbest0 Hanswer1]].
    subst i best answer.
    split.
    + lia.
    + right.
      split; [lia |].
      split; [lia |].
      split.
      * replace (0 + 1 - 1) with 0 by lia.
        exact Hcurrent.
      * split.
        -- intros j Hj.
           assert (Hj0 : j = 0) by lia.
           rewrite Hj0.
           rewrite Hcurrent.
           lia.
        -- intros j Hj.
           lia.
  - destruct Hpositive as [Hi_pos [Hanswer [Hbest [Hmaximum Hlast]]]].
    split.
    + lia.
    + right.
      split; [lia |].
      split; [lia |].
      split.
      * replace (i + 1 - 1) with i by lia.
        exact Hcurrent.
      * split.
        -- intros j Hj.
           destruct (Z.eq_dec j i) as [Hji | Hji].
           ++ subst j.
              rewrite Hcurrent.
              lia.
           ++ eapply Z.le_trans.
              ** apply Hmaximum.
                 lia.
              ** exact Hge.
        -- intros j Hj.
           lia.
Qed.
Lemma last_max_prefix_update_lt__prefix_updates :
  forall m wants i best answer current,
    0 <= current ->
    0 <= i < Zlength wants ->
    LastMaxPrefix m wants i best answer ->
    current = CandyTurns m (Znth i wants 0) ->
    current < best ->
    LastMaxPrefix m wants (i + 1) best answer.
Proof.
  intros m wants i best answer current Hcurrent_nonneg Hi Hprefix Hcurrent Hlt.
  unfold LastMaxPrefix in *.
  destruct Hprefix as [Hbounds [Hzero | Hpositive]].
  - destruct Hzero as [Hi0 [Hbest0 Hanswer1]].
    subst i best answer.
    lia.
  - destruct Hpositive as [Hi_pos [Hanswer [Hbest [Hmaximum Hlast]]]].
    split.
    + lia.
    + right.
      split; [lia |].
      split; [lia |].
      split; [exact Hbest |].
      split.
      * intros j Hj.
        destruct (Z.eq_dec j i) as [Hji | Hji].
        -- subst j.
           rewrite <- Hcurrent.
           lia.
        -- apply Hmaximum.
           lia.
      * intros j Hj.
        destruct (Z.eq_dec j i) as [Hji | Hji].
        -- subst j.
           rewrite <- Hcurrent.
           exact Hlt.
        -- apply Hlast.
           lia.
Qed.
Lemma candy_turns_pos__final_trace :
  forall m need,
    0 < m -> 0 < need -> 1 <= CandyTurns m need.
Proof.
  intros m need Hm Hneed.
  unfold CandyTurns.
  replace (need + m - 1) with ((need - 1) + 1 * m) by ring.
  rewrite Z.div_add by lia.
  pose proof (Z.div_pos (need - 1) m ltac:(lia) Hm).
  lia.
Qed.
Lemma candy_turns_small__final_trace :
  forall m need,
    0 < m -> 0 < need <= m -> CandyTurns m need = 1.
Proof.
  intros m need Hm Hneed.
  unfold CandyTurns.
  replace (need + m - 1) with ((need - 1) + 1 * m) by ring.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia.
  reflexivity.
Qed.
Lemma candy_turns_sub__final_trace :
  forall m need,
    0 < m -> m < need ->
    CandyTurns m (need - m) = CandyTurns m need - 1.
Proof.
  intros m need Hm Hneed.
  unfold CandyTurns.
  replace (need - m + m - 1) with (need - 1) by ring.
  replace (need + m - 1) with ((need - 1) + 1 * m) by ring.
  rewrite Z.div_add by lia.
  lia.
Qed.
Lemma candy_queue_trace_cons__final_trace :
  forall m before after states answer need rest,
    OneCandyTurn m before after ->
    CandyQueueTrace m after states ->
    Znth (Zlength states - 2) states [] = (answer, need) :: rest ->
    CandyQueueTrace m before (before :: states) /\
    Znth (Zlength (before :: states) - 2) (before :: states) [] =
      (answer, need) :: rest.
Proof.
  intros m before after states answer need rest Hturn Htrace Hlast.
  destruct Htrace as [Hlen [Hfirst [Hempty Hsteps]]].
  split.
  - unfold CandyQueueTrace.
    rewrite Zlength_cons.
    split; [lia |].
    split; [reflexivity |].
    split.
    + rewrite Znth_cons by lia.
      replace (Z.succ (Zlength states) - 1 - 1) with
          (Zlength states - 1) by (unfold Z.succ; lia).
      exact Hempty.
    + intros k Hk.
      destruct (Z.eq_dec k 0) as [-> | Hk0].
      * change (OneCandyTurn m before (Znth 0 states [])).
        rewrite Hfirst.
        exact Hturn.
      * rewrite (Znth_cons [] k before states) by lia.
        rewrite (Znth_cons [] (k + 1) before states) by lia.
        replace (k + 1 - 1) with k by lia.
        specialize (Hsteps (k - 1) ltac:(unfold Z.succ in Hk; lia)).
        replace (k - 1 + 1) with k in Hsteps by lia.
        exact Hsteps.
  - rewrite Zlength_cons.
    rewrite Znth_cons by lia.
    replace (Z.succ (Zlength states) - 2 - 1) with
        (Zlength states - 2) by (unfold Z.succ; lia).
    exact Hlast.
Qed.
Lemma candy_measure_tail_lt__final_trace :
  forall child need tail,
    0 < need ->
    (fold_right Nat.add 0
       (map (fun p : Z * Z => Z.to_nat (snd p)) tail) <
     fold_right Nat.add 0
       (map (fun p : Z * Z => Z.to_nat (snd p))
          ((child, need) :: tail)))%nat.
Proof.
  intros child need tail Hneed.
  simpl.
  assert ((0 < Z.to_nat need)%nat).
  { apply (proj1 (Z2Nat.inj_lt 0 need ltac:(lia) ltac:(lia))). lia. }
  lia.
Qed.
Lemma candy_measure_rotate_lt__final_trace :
  forall m child need tail,
    0 < m -> m < need ->
    (fold_right Nat.add 0
       (map (fun p : Z * Z => Z.to_nat (snd p))
          (tail ++ [(child, (need - m)%Z)])) <
     fold_right Nat.add 0
       (map (fun p : Z * Z => Z.to_nat (snd p))
          ((child, need) :: tail)))%nat.
Proof.
  intros m child need tail Hm Hneed.
  assert ((Z.to_nat (need - m) < Z.to_nat need)%nat).
  { apply (proj1 (Z2Nat.inj_lt (need - m) need ltac:(lia) ltac:(lia))).
    lia. }
  induction tail as [| [other other_need] tail IH].
  - simpl. lia.
  - simpl in *. lia.
Qed.
Lemma candy_queue_trace_from_last_max__final_trace :
  forall m q answer best,
    0 < m ->
    Forall (fun p : Z * Z => 0 < snd p) q ->
    (exists prefix chosen_need suffix,
      q = prefix ++ (answer, chosen_need) :: suffix /\
      CandyTurns m chosen_need = best /\
      Forall (fun p : Z * Z => CandyTurns m (snd p) <= best) prefix /\
      Forall (fun p : Z * Z => CandyTurns m (snd p) < best) suffix) ->
    exists states need rest,
      CandyQueueTrace m q states /\
      Znth (Zlength states - 2) states [] = (answer, need) :: rest.
Proof.
  intros m q answer best Hm Hpositive Hlastmax.
  assert (Hstrong : forall fuel : nat,
    forall q answer best,
      (fold_right Nat.add 0
         (map (fun p : Z * Z => Z.to_nat (snd p)) q) <= fuel)%nat ->
      Forall (fun p : Z * Z => 0 < snd p) q ->
      (exists prefix chosen_need suffix,
        q = prefix ++ (answer, chosen_need) :: suffix /\
        CandyTurns m chosen_need = best /\
        Forall (fun p : Z * Z => CandyTurns m (snd p) <= best) prefix /\
        Forall (fun p : Z * Z => CandyTurns m (snd p) < best) suffix) ->
      exists states need rest,
        CandyQueueTrace m q states /\
        Znth (Zlength states - 2) states [] = (answer, need) :: rest).
  {
    intros fuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros q0 answer0 best0 Hfuel Hpos Hmax.
    destruct Hmax as
      (prefix & chosen_need & suffix & Hq & Hchosen & Hprefix & Hsuffix).
    destruct q0 as [| [child head_need] tail].
    { exfalso.
      pose proof (f_equal (@length (Z * Z)) Hq).
      rewrite length_app in H. simpl in H. lia. }
    inversion Hpos as [| first tail0 Hhead Htail]; subst first tail0.
    simpl in Hhead.
    destruct (Z_le_gt_dec head_need m) as [Hsmall | Hlarge].
    - destruct prefix as [| [prefix_child prefix_need] prefix_tail].
      + simpl in Hq.
        inversion Hq; subst child head_need tail.
        assert (Hbest : best0 = 1).
        { rewrite <- Hchosen.
          apply candy_turns_small__final_trace; lia. }
        destruct suffix as [| [suffix_child suffix_need] suffix_tail].
        * exists [[(answer0, chosen_need)]; []], chosen_need, [].
          split.
          -- unfold CandyQueueTrace.
             simpl.
             repeat split; try lia; try reflexivity.
             intros k Hk.
             assert (k = 0) by lia. subst k.
             unfold OneCandyTurn.
             exists answer0, chosen_need, [].
             simpl.
             tauto.
          -- reflexivity.
        * inversion Htail as [| suffix_first suffix_tail0 Hsuffix_need Htail'];
            subst suffix_first suffix_tail0.
          inversion Hsuffix as [| suffix_first suffix_tail0 Hsuffix_turn Hsuffix'];
            subst suffix_first suffix_tail0.
          simpl in Hsuffix_need, Hsuffix_turn.
          pose proof (candy_turns_pos__final_trace m suffix_need Hm Hsuffix_need).
          lia.
      + simpl in Hq.
        inversion Hq; subst child head_need tail.
        inversion Hprefix as [| prefix_first prefix_tail0 Hhead_turn Hprefix'];
          subst prefix_first prefix_tail0.
        assert (Hmeasure :
          (fold_right Nat.add 0
             (map (fun p : Z * Z => Z.to_nat (snd p))
                (prefix_tail ++ (answer0, chosen_need) :: suffix)) < fuel)%nat).
        { eapply Nat.lt_le_trans.
          - apply candy_measure_tail_lt__final_trace. exact Hhead.
          - exact Hfuel. }
        specialize (IH _ Hmeasure
          (prefix_tail ++ (answer0, chosen_need) :: suffix)
          answer0 best0 ltac:(lia) Htail).
        specialize (IH ltac:(exists prefix_tail, chosen_need, suffix;
          repeat split; assumption)).
        destruct IH as (states & final_need & final_rest & Htrace & Hfinal).
        exists (((prefix_child, prefix_need) ::
          (prefix_tail ++ (answer0, chosen_need) :: suffix)) :: states).
        exists final_need, final_rest.
        eapply candy_queue_trace_cons__final_trace.
        * unfold OneCandyTurn.
          exists prefix_child, prefix_need,
            (prefix_tail ++ (answer0, chosen_need) :: suffix).
          split; [reflexivity |].
          left. split; [exact Hsmall | reflexivity].
        * exact Htrace.
        * exact Hfinal.
    - assert (Hremaining : 0 < head_need - m) by lia.
      assert (Hmeasure :
        (fold_right Nat.add 0
           (map (fun p : Z * Z => Z.to_nat (snd p))
              (tail ++ [(child, (head_need - m)%Z)])) < fuel)%nat).
      { eapply Nat.lt_le_trans.
        - apply candy_measure_rotate_lt__final_trace; [exact Hm | lia].
        - exact Hfuel. }
      assert (Hpos' : Forall (fun p : Z * Z => 0 < snd p)
        (tail ++ [(child, head_need - m)])).
      { apply Forall_app. split; [exact Htail |].
        constructor; [simpl; lia | constructor]. }
      destruct prefix as [| [prefix_child prefix_need] prefix_tail].
      + simpl in Hq.
        inversion Hq; subst child head_need tail.
        assert (Hchosen' :
          CandyTurns m (chosen_need - m) = best0 - 1).
        { rewrite candy_turns_sub__final_trace by lia. lia. }
        assert (Hprefix' :
          Forall (fun p : Z * Z => CandyTurns m (snd p) <= best0 - 1)
            suffix).
        { eapply Forall_impl; [| exact Hsuffix].
          intros [other other_need] Hother. simpl in *. lia. }
        specialize (IH _ Hmeasure
          (suffix ++ [(answer0, chosen_need - m)])
          answer0 (best0 - 1) ltac:(lia) Hpos').
        specialize (IH ltac:(exists suffix, (chosen_need - m), [];
          repeat split; try assumption; simpl; try constructor;
          rewrite app_assoc; reflexivity)).
        destruct IH as (states & final_need & final_rest & Htrace & Hfinal).
        exists (((answer0, chosen_need) :: suffix) :: states).
        exists final_need, final_rest.
        eapply candy_queue_trace_cons__final_trace.
        * unfold OneCandyTurn.
          exists answer0, chosen_need, suffix.
          split; [reflexivity |].
          right. split; [lia | reflexivity].
        * exact Htrace.
        * exact Hfinal.
      + simpl in Hq.
        inversion Hq; subst child head_need tail.
        inversion Hprefix as [| prefix_first prefix_tail0 Hhead_turn Hprefix'];
          subst prefix_first prefix_tail0.
        simpl in Hhead_turn.
        assert (Hhead_turn' :
          CandyTurns m (prefix_need - m) < best0).
        { rewrite candy_turns_sub__final_trace by lia. lia. }
        specialize (IH _ Hmeasure
          ((prefix_tail ++ (answer0, chosen_need) :: suffix) ++
             [(prefix_child, prefix_need - m)])
          answer0 best0 ltac:(lia) Hpos').
        specialize (IH ltac:(exists prefix_tail, chosen_need,
          (suffix ++ [(prefix_child, prefix_need - m)]);
          repeat split; try assumption;
          [change ((prefix_tail ++ ((answer0, chosen_need) :: suffix)) ++
             [(prefix_child, prefix_need - m)] =
             prefix_tail ++ (((answer0, chosen_need) :: suffix) ++
             [(prefix_child, prefix_need - m)]));
           symmetry; apply app_assoc |
           apply Forall_app; split; [assumption | constructor; simpl;
             [assumption | constructor]]])).
        destruct IH as (states & final_need & final_rest & Htrace & Hfinal).
        exists (((prefix_child, prefix_need) ::
          (prefix_tail ++ (answer0, chosen_need) :: suffix)) :: states).
        exists final_need, final_rest.
        eapply candy_queue_trace_cons__final_trace.
        * unfold OneCandyTurn.
          exists prefix_child, prefix_need,
            (prefix_tail ++ (answer0, chosen_need) :: suffix).
          split; [reflexivity |].
          right. split; [lia | reflexivity].
        * exact Htrace.
        * exact Hfinal.
  }
  eapply Hstrong with
    (fuel := fold_right Nat.add 0%nat
      (map (fun p : Z * Z => Z.to_nat (snd p)) q)); eauto.
Qed.
Lemma last_max_prefix_full_last_argmax__final_trace :
  forall m wants best answer,
    0 < Zlength wants ->
    LastMaxPrefix m wants (Zlength wants) best answer ->
    1 <= answer <= Zlength wants /\
    best = CandyTurns m (Znth (answer - 1) wants 0) /\
    (forall j, 0 <= j < Zlength wants ->
      CandyTurns m (Znth j wants 0) <= best) /\
    (forall j, answer <= j < Zlength wants ->
      CandyTurns m (Znth j wants 0) < best).
Proof.
  intros m wants best answer Hlen Hmax.
  unfold LastMaxPrefix in Hmax.
  destruct Hmax as [_ [Hzero | Hnonzero]].
  - lia.
  - tauto.
Qed.
Lemma zrange_aux_length__final_trace :
  forall start n,
    length (Zrange_aux start n) = n.
Proof.
  intros start n. revert start.
  induction n as [| n IH]; intros start; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma zrange_aux_nth__final_trace :
  forall start n i,
    (i < n)%nat ->
    nth i (Zrange_aux start n) 0 = start + Z.of_nat i.
Proof.
  intros start n. revert start.
  induction n as [| n IH]; intros start i Hi.
  - lia.
  - destruct i as [| i].
    + simpl. lia.
    + simpl. rewrite IH by lia. lia.
Qed.
Lemma indexed_candy_queue_length__final_trace :
  forall wants : list Z,
    Zlength
      (combine (Zrange 1 (Zlength wants + 1)) wants) = Zlength wants.
Proof.
  intros wants.
  unfold Zrange.
  rewrite !Zlength_correct, length_combine, zrange_aux_length__final_trace.
  replace (Z.to_nat (Z.of_nat (length wants) + 1 - 1))
    with (length wants) by lia.
  lia.
Qed.
Lemma indexed_candy_queue_Znth__final_trace :
  forall wants j,
    0 <= j < Zlength wants ->
    Znth j (combine (Zrange 1 (Zlength wants + 1)) wants) (0, 0) =
      (j + 1, Znth j wants 0).
Proof.
  intros wants j Hj.
  unfold Znth at 1.
  unfold Zrange.
  replace (Z.to_nat (Zlength wants + 1 - 1)) with (length wants)
    by (rewrite Zlength_correct; lia).
  rewrite combine_nth.
  - rewrite zrange_aux_nth__final_trace by (rewrite Zlength_correct in Hj; lia).
    unfold Znth.
    f_equal. lia.
  - rewrite zrange_aux_length__final_trace. reflexivity.
Qed.
Lemma Zlength_skipn_Z__final_trace :
  forall (A : Type) (l : list A) n,
    0 <= n <= Zlength l ->
    Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros A l n Hn.
  rewrite Zlength_correct in Hn.
  rewrite !Zlength_correct, length_skipn.
  rewrite Nat2Z.inj_sub by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma Znth_skipn_Z__final_trace :
  forall (A : Type) (d : A) (l : list A) n j,
    0 <= n -> 0 <= j ->
    Znth j (skipn (Z.to_nat n) l) d = Znth (n + j) l d.
Proof.
  intros A d l n j Hn Hj.
  unfold Znth.
  rewrite nth_skipn.
  f_equal. lia.
Qed.
Lemma list_split_nth__final_trace :
  forall (A : Type) (n : nat) (l : list A) (d : A),
    (n < length l)%nat ->
    l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  intros A n l d Hn.
  apply firstn_skipSn.
  exact Hn.
Qed.
Lemma indexed_candy_queue_last_max_decomposition__final_trace :
  forall m wants best answer,
    1 <= answer <= Zlength wants ->
    best = CandyTurns m (Znth (answer - 1) wants 0) ->
    (forall j, 0 <= j < Zlength wants ->
      CandyTurns m (Znth j wants 0) <= best) ->
    (forall j, answer <= j < Zlength wants ->
      CandyTurns m (Znth j wants 0) < best) ->
    exists prefix chosen_need suffix,
      combine (Zrange 1 (Zlength wants + 1)) wants =
        prefix ++ (answer, chosen_need) :: suffix /\
      CandyTurns m chosen_need = best /\
      Forall (fun p : Z * Z => CandyTurns m (snd p) <= best) prefix /\
      Forall (fun p : Z * Z => CandyTurns m (snd p) < best) suffix.
Proof.
  intros m wants best answer Hans Hbest Hall Hlater.
  set (queue := combine (Zrange 1 (Zlength wants + 1)) wants).
  assert (Hqlen : Zlength queue = Zlength wants).
  { unfold queue. apply indexed_candy_queue_length__final_trace. }
  assert (Hidx :
    (Z.to_nat (answer - 1) < length queue)%nat).
  { replace (length queue) with (Z.to_nat (Zlength queue))
      by (rewrite Zlength_correct; lia).
    rewrite Hqlen. lia. }
  pose proof (list_split_nth__final_trace (Z * Z) (Z.to_nat (answer - 1))
    queue (0, 0) Hidx) as Hsplit.
  assert (Hnth :
    nth (Z.to_nat (answer - 1)) queue (0, 0) =
      (answer, Znth (answer - 1) wants 0)).
  { change (Znth (answer - 1) queue (0, 0) =
      (answer, Znth (answer - 1) wants 0)).
    unfold queue.
    rewrite indexed_candy_queue_Znth__final_trace by lia.
    f_equal. lia. }
  rewrite Hnth in Hsplit.
  assert (Hfull :
    Forall (fun p : Z * Z => CandyTurns m (snd p) <= best) queue).
  { apply (proj2 (Forall_Znth
      (fun p : Z * Z => CandyTurns m (snd p) <= best) (0, 0) queue)).
    intros j Hj.
    unfold queue.
    rewrite indexed_candy_queue_Znth__final_trace by (rewrite Hqlen in Hj; lia).
    simpl. apply Hall. rewrite <- Hqlen. exact Hj. }
  rewrite Hsplit in Hfull.
  apply Forall_app in Hfull.
  destruct Hfull as [Hprefix _].
  assert (Hsuffix :
    Forall (fun p : Z * Z => CandyTurns m (snd p) < best)
      (skipn (S (Z.to_nat (answer - 1))) queue)).
  { apply (proj2 (Forall_Znth
      (fun p : Z * Z => CandyTurns m (snd p) < best) (0, 0)
      (skipn (S (Z.to_nat (answer - 1))) queue))).
    intros j Hj.
    replace (S (Z.to_nat (answer - 1))) with (Z.to_nat answer) in * by lia.
    assert (Hbound : answer <= answer + j < Zlength wants).
    { rewrite <- Hqlen.
      rewrite Zlength_skipn_Z__final_trace in Hj by (rewrite Hqlen; lia).
      lia. }
    rewrite Znth_skipn_Z__final_trace by lia.
    unfold queue.
    rewrite indexed_candy_queue_Znth__final_trace by lia.
    simpl. apply Hlater. exact Hbound. }
  exists (firstn (Z.to_nat (answer - 1)) queue),
    (Znth (answer - 1) wants 0),
    (skipn (S (Z.to_nat (answer - 1))) queue).
  split; [exact Hsplit |].
  split; [symmetry; exact Hbest |].
  split; assumption.
Qed.
Lemma candy_queue_trace_last_argmax__final_trace :
  forall m wants best answer,
    0 < m ->
    0 < Zlength wants ->
    (forall j, 0 <= j < Zlength wants -> 0 < Znth j wants 0) ->
    LastMaxPrefix m wants (Zlength wants) best answer ->
    exists states need rest,
      CandyQueueTrace m
        (combine (Zrange 1 (Zlength wants + 1)) wants) states /\
      Znth (Zlength states - 2) states [] = (answer, need) :: rest.
Proof.
  intros m wants best answer Hm Hlen Hpositive Hmax.
  pose proof (last_max_prefix_full_last_argmax__final_trace
    m wants best answer Hlen Hmax) as Hfacts.
  destruct Hfacts as [Hanswer [Hbest [Hall Hlater]]].
  pose proof (indexed_candy_queue_last_max_decomposition__final_trace
    m wants best answer Hanswer Hbest Hall Hlater) as Hdecomp.
  assert (Hqueuepos :
    Forall (fun p : Z * Z => 0 < snd p)
      (combine (Zrange 1 (Zlength wants + 1)) wants)).
  { apply (proj2 (Forall_Znth (fun p : Z * Z => 0 < snd p) (0, 0)
      (combine (Zrange 1 (Zlength wants + 1)) wants))).
    intros j Hj.
    rewrite indexed_candy_queue_Znth__final_trace.
    - simpl. apply Hpositive.
      rewrite indexed_candy_queue_length__final_trace in Hj.
      exact Hj.
    - rewrite indexed_candy_queue_length__final_trace in Hj.
      exact Hj. }
  eapply candy_queue_trace_from_last_max__final_trace; eauto.
Qed.
