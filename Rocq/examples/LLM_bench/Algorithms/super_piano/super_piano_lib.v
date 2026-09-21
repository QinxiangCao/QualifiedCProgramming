Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Require Export SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
From SumLib Require Import ZRange.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ST_LEVELS : Z := 17.

Definition PrefixArrayPrefix
    (l pref : list Z) (upto : Z) : Prop :=
  Zlength pref = upto + 1 /\
  Znth 0 pref 0 = 0 /\
  forall i,
    0 <= i < upto ->
    Znth (i + 1) pref 0 = Znth i pref 0 + Znth i l 0.

Definition PrefixSums (l pref : list Z) : Prop :=
  Zlength pref = Zlength l + 1 /\
  forall i, 0 <= i <= Zlength l -> Znth i pref 0 = sum (sublist 0 i l).

Lemma piano_sum_prefix_step l i :
  0 <= i < Zlength l ->
  sum (sublist 0 (i+1) l) = sum (sublist 0 i l) + Znth i l 0.
Proof.
  intros Hi. rewrite (sublist_split 0 (i+1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia. rewrite sum_app. cbn. lia.
Qed.

Lemma PrefixSums_recurrence l pref :
  PrefixSums l pref <-> PrefixArrayPrefix l pref (Zlength l).
Proof.
  unfold PrefixSums, PrefixArrayPrefix. split.
  - intros [Hlen Hall]. split; [exact Hlen|]. split.
    + specialize (Hall 0 ltac:(pose proof (Zlength_nonneg l);lia)).
      rewrite Zsublist_nil in Hall by lia. exact Hall.
    + intros i Hi.
      rewrite (Hall (i+1) ltac:(lia)), (Hall i ltac:(lia)).
      apply piano_sum_prefix_step. exact Hi.
  - intros [Hlen [Hzero Hstep]]. split; [exact Hlen|].
    assert (Hmain : forall k, Z.of_nat k <= Zlength l ->
      Znth (Z.of_nat k) pref 0 = sum (sublist 0 (Z.of_nat k) l)).
    { induction k as [|k IH]; intro Hk.
      - cbn. exact Hzero.
      - replace (Z.of_nat (S k)) with (Z.of_nat k+1) by lia.
        rewrite Hstep by lia. rewrite piano_sum_prefix_step by lia.
        rewrite IH by lia. reflexivity. }
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    apply Hmain. lia.
Qed.

Definition RangeArgmax (ps : list Z) (lo hi best : Z) : Prop :=
  max_value_of_subset (fun i j => Znth i ps 0 <= Znth j ps 0)
    (fun i : Z => lo <= i <= hi) (fun i : Z => i) best.

Lemma RangeArgmax_unfold ps lo hi best :
  RangeArgmax ps lo hi best <->
  lo <= best /\ best <= hi /\
  forall idx, lo <= idx <= hi -> Znth idx ps 0 <= Znth best ps 0.
Proof.
  unfold RangeArgmax, max_value_of_subset, max_object_of_subset. cbn beta.
  split.
  - intros [p [[Hp Hmax] Heq]]. subst p. change (lo<=best<=hi) in Hp.
    split; [tauto|]. split; [tauto|]. exact Hmax.
  - intros [Hlo [Hhi Hmax]]. exists best. split; [split |reflexivity]; [split;assumption|exact Hmax].
Qed.

Lemma Piano_max_at (f : Z -> Z) lo hi best value :
  lo <= best <= hi -> f best = value ->
  (max_value_of_subset Z.le (fun p : Z => lo <= p <= hi) f value <->
   forall p, lo <= p <= hi -> f p <= value).
Proof.
  intros Hbest Hvalue. unfold max_value_of_subset, max_object_of_subset. split.
  - intros [p [[Hp Hmax] Heq]] q Hq. specialize (Hmax q Hq). lia.
  - intros Hmax. exists best. split; [split |exact Hvalue];
    [exact Hbest |intros q Hq; specialize (Hmax q Hq); lia].
Qed.

Definition Node := (Z * Z * Z * Z * Z)%type.

Definition default_node : Node := (0, 0, 0, 0, 0).

Definition mkNode
    (value start lo hi best : Z) : Node :=
  (value, start, lo, hi, best).

Definition node_value (nd : Node) : Z :=
  let '(v, _, _, _, _) := nd in v.

Definition node_start (nd : Node) : Z :=
  let '(_, s, _, _, _) := nd in s.

Definition node_lo (nd : Node) : Z :=
  let '(_, _, lo, _, _) := nd in lo.

Definition node_hi (nd : Node) : Z :=
  let '(_, _, _, hi, _) := nd in hi.

Definition node_best (nd : Node) : Z :=
  let '(_, _, _, _, best) := nd in best.

Definition heap_top_node (slots : list Node) : Node :=
  Znth 0 slots default_node.

Definition heap_top_value (slots : list Node) : Z :=
  node_value (heap_top_node slots).

Definition heap_top_start (slots : list Node) : Z :=
  node_start (heap_top_node slots).

Definition heap_top_lo (slots : list Node) : Z :=
  node_lo (heap_top_node slots).

Definition heap_top_hi (slots : list Node) : Z :=
  node_hi (heap_top_node slots).

Definition heap_top_best (slots : list Node) : Z :=
  node_best (heap_top_node slots).

Definition NodeArrays
    (slots : list Node)
    (vals starts los his bests : list Z) : Prop :=
  Forall2 (fun v nd => v = node_value nd) vals slots /\
  Forall2 (fun v nd => v = node_start nd) starts slots /\
  Forall2 (fun v nd => v = node_lo nd) los slots /\
  Forall2 (fun v nd => v = node_hi nd) his slots /\
  Forall2 (fun v nd => v = node_best nd) bests slots.

Definition NodeHeapState (slots : list Node) (size : Z) : Prop :=
  heap_ordered (map node_value slots) size /\
  (sublist 0 size slots = [] \/
   max_value_of_subset Z.le
     (fun nd => In nd (sublist 0 size slots)) node_value (heap_top_value slots)).

Definition FrontierPushPrefix
    (slots : list Node) (size : Z) (nd : Node) (slots_out : list Node) : Prop :=
  Zlength slots_out = Zlength slots /\
  Permutation
    (nd :: sublist 0 size slots)
    (sublist 0 (size + 1) slots_out).

Definition FrontierPopPrefix
    (slots : list Node) (size : Z) (popped : Node) (slots_out : list Node) : Prop :=
  Zlength slots_out = Zlength slots /\
  In popped (sublist 0 size slots) /\
  Permutation
    (popped :: sublist 0 (size - 1) slots_out)
    (sublist 0 size slots).

Definition FrontierPushFields
    (slots : list Node) (size value start lo hi best : Z)
    (slots_out : list Node) : Prop :=
  FrontierPushPrefix slots size (value, start, lo, hi, best) slots_out.

Definition FrontierPopTop
    (slots : list Node) (size : Z) (slots_out : list Node) : Prop :=
  FrontierPopPrefix slots size (heap_top_node slots) slots_out.

Definition ChordCode (n start finish : Z) : Z :=
  start * (n + 1) + finish.

Definition CodeStart (n code : Z) : Z :=
  code / (n + 1).

Definition CodeEnd (n code : Z) : Z :=
  code mod (n + 1).

Definition ChordValueOfCode (ps : list Z) (n code : Z) : Z :=
  Znth (CodeEnd n code) ps 0 - Znth (CodeStart n code - 1) ps 0.

Definition ValidChordCode
    (ps : list Z) (n L R code : Z) : Prop :=
  Zlength ps = n + 1 /\
  1 <= CodeStart n code /\
  CodeStart n code <= CodeEnd n code /\
  CodeEnd n code <= n /\
  L <= CodeEnd n code - CodeStart n code + 1 /\
  CodeEnd n code - CodeStart n code + 1 <= R.

Definition SongCodesSum
    (ps : list Z) (n : Z) (codes : list Z) (total : Z) : Prop :=
  total = sum (map (fun code => ChordValueOfCode ps n code) codes).

Definition ValidSongCodes
    (ps : list Z) (n L R k : Z) (codes : list Z) : Prop :=
  Zlength codes = k /\
  NoDup codes /\
  Forall (ValidChordCode ps n L R) codes.

Definition SuperPianoAnswerByPrefix
    (ps : list Z) (n L R k answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun codes => ValidSongCodes ps n L R k codes)
    (fun codes => sum (map (fun code => ChordValueOfCode ps n code) codes))
    answer.

Definition ValidNode
    (ps : list Z) (n L R : Z) (nd : Node) : Prop :=
  Zlength ps = n + 1 /\
  1 <= node_start nd /\
  node_start nd <= n /\
  node_start nd + L - 1 <= node_lo nd /\
  node_lo nd <= node_hi nd /\
  node_hi nd <= Z.min n (node_start nd + R - 1) /\
  node_lo nd <= node_best nd /\
  node_best nd <= node_hi nd /\
  node_value nd =
    Znth (node_best nd) ps 0 - Znth (node_start nd - 1) ps 0 /\
  max_value_of_subset Z.le
    (fun finish : Z => node_lo nd <= finish <= node_hi nd)
    (fun finish => Znth finish ps 0 - Znth (node_start nd - 1) ps 0)
    (node_value nd).

Lemma ValidNode_unfold ps n L R nd :
  ValidNode ps n L R nd <->
  Zlength ps = n + 1 /\
  1 <= node_start nd /\ node_start nd <= n /\
  node_start nd + L - 1 <= node_lo nd /\ node_lo nd <= node_hi nd /\
  node_hi nd <= Z.min n (node_start nd + R - 1) /\
  node_lo nd <= node_best nd /\ node_best nd <= node_hi nd /\
  node_value nd = Znth (node_best nd) ps 0 - Znth (node_start nd - 1) ps 0 /\
  forall finish, node_lo nd <= finish <= node_hi nd ->
    Znth finish ps 0 - Znth (node_start nd - 1) ps 0 <= node_value nd.
Proof.
  unfold ValidNode. split;
    intros (Hlen&Hstart&Hend&Hlo&Hnonempty&Hhi&Hbestlo&Hbesthi&Hvalue&Hmax);
    do 9 (split; [assumption|]).
  - apply (proj1 (Piano_max_at (fun finish => Znth finish ps 0 - Znth (node_start nd - 1) ps 0) (node_lo nd) (node_hi nd) (node_best nd) (node_value nd) ltac:(lia) ltac:(symmetry;exact Hvalue))). exact Hmax.
  - apply (proj2 (Piano_max_at (fun finish => Znth finish ps 0 - Znth (node_start nd - 1) ps 0) (node_lo nd) (node_hi nd) (node_best nd) (node_value nd) ltac:(lia) ltac:(symmetry;exact Hvalue))). exact Hmax.
Qed.


Definition ValidNodeFields
    (ps : list Z) (n L R value start lo hi best : Z) : Prop :=
  ValidNode ps n L R (value, start, lo, hi, best).

Definition NodeCoversCode
    (n : Z) (nd : Node) (code : Z) : Prop :=
  CodeStart n code = node_start nd /\
  node_lo nd <= CodeEnd n code <= node_hi nd.

Definition ChosenDominatesRemaining
    (ps : list Z) (n L R : Z) (chosen : list Z) : Prop :=
  forall picked rest,
    In picked chosen ->
    ValidChordCode ps n L R rest ->
    ~ In rest chosen ->
    ChordValueOfCode ps n rest <= ChordValueOfCode ps n picked.

Definition DisjointClosed
    (lo1 hi1 lo2 hi2 : Z) : Prop :=
  hi1 < lo2 \/ hi2 < lo1.

Definition NodesDisjointForSameStart
    (nodes : list Node) : Prop :=
  NoDup nodes /\
  forall nd1 nd2,
    In nd1 nodes ->
    In nd2 nodes ->
    nd1 <> nd2 ->
    node_start nd1 = node_start nd2 ->
    DisjointClosed
      (node_lo nd1) (node_hi nd1)
      (node_lo nd2) (node_hi nd2).

Definition NodesCoverRemaining
    (ps : list Z) (n L R : Z)
    (chosen : list Z) (nodes : list Node) : Prop :=
  forall code,
    ValidChordCode ps n L R code ->
    ~ In code chosen ->
    exists nd,
      In nd nodes /\
      NodeCoversCode n nd code.

Definition NodesExcludeChosen
    (n : Z) (chosen : list Z) (nodes : list Node) : Prop :=
  forall nd code,
    In nd nodes ->
    NodeCoversCode n nd code ->
    ~ In code chosen.

Definition FrontierState
    (ps : list Z) (n L R : Z)
    (chosen : list Z) (chosen_len total : Z)
    (nodes : list Node) : Prop :=
  ValidSongCodes ps n L R chosen_len chosen /\
  SongCodesSum ps n chosen total /\
  ChosenDominatesRemaining ps n L R chosen /\
  Forall (ValidNode ps n L R) nodes /\
  NodesDisjointForSameStart nodes /\
  NodesCoverRemaining ps n L R chosen nodes /\
  NodesExcludeChosen n chosen nodes.

Definition FrontierSplitState
    (ps : list Z) (n L R : Z)
    (chosen : list Z) (chosen_len total : Z)
    (pending nodes : list Node) : Prop :=
  FrontierState ps n L R chosen chosen_len total (app pending nodes).

Definition InitialFrontierState
    (ps : list Z) (n L R : Z) (nodes : list Node) : Prop :=
  FrontierState ps n L R [] 0 0 nodes.

Lemma Forall_permutation : forall {A : Type} (P : A -> Prop) l l',
  Permutation l l' ->
  Forall P l ->
  Forall P l'.
Proof.
  intros A P l l' Hperm Hfor.
  apply Forall_forall.
  intros x Hinx.
  apply (proj1 (Forall_forall P l) Hfor).
  eapply Permutation_in.
  - apply Permutation_sym; exact Hperm.
  - exact Hinx.
Qed.

Lemma NodesDisjointForSameStart_permutation : forall nodes nodes',
  Permutation nodes nodes' ->
  NodesDisjointForSameStart nodes ->
  NodesDisjointForSameStart nodes'.
Proof.
  intros nodes nodes' Hperm [Hnodup Hdisjoint].
  split.
  - eapply Permutation_NoDup; eauto.
  - intros nd1 nd2 Hin1 Hin2 Hneq Hsame_start.
    eapply Hdisjoint; eauto.
    + eapply Permutation_in.
      * apply Permutation_sym; exact Hperm.
      * exact Hin1.
    + eapply Permutation_in.
      * apply Permutation_sym; exact Hperm.
      * exact Hin2.
Qed.

Lemma NodesCoverRemaining_permutation :
  forall ps n L R chosen nodes nodes',
    Permutation nodes nodes' ->
    NodesCoverRemaining ps n L R chosen nodes ->
    NodesCoverRemaining ps n L R chosen nodes'.
Proof.
  intros ps n L R chosen nodes nodes' Hperm Hcover code Hvalid Hnotin.
  destruct (Hcover code Hvalid Hnotin) as [nd [Hin Hcovers]].
  exists nd.
  split.
  - eapply Permutation_in.
    + exact Hperm.
    + exact Hin.
  - exact Hcovers.
Qed.

Lemma NodesExcludeChosen_permutation :
  forall n chosen nodes nodes',
    Permutation nodes nodes' ->
    NodesExcludeChosen n chosen nodes ->
    NodesExcludeChosen n chosen nodes'.
Proof.
  intros n chosen nodes nodes' Hperm Hexclude nd code Hin Hcovers.
  eapply Hexclude; eauto.
  eapply Permutation_in.
  - apply Permutation_sym; exact Hperm.
  - exact Hin.
Qed.

Lemma FrontierState_permutation :
  forall ps n L R chosen chosen_len total nodes nodes',
    Permutation nodes nodes' ->
    FrontierState ps n L R chosen chosen_len total nodes ->
    FrontierState ps n L R chosen chosen_len total nodes'.
Proof.
  intros ps n L R chosen chosen_len total nodes nodes' Hperm
    [Hcodes [Hsum [Hdom [Hvalid [Hdisjoint [Hcover Hexclude]]]]]].
  split; [exact Hcodes|].
  split; [exact Hsum|].
  split; [exact Hdom|].
  split.
  - eapply Forall_permutation; eauto.
  - split.
    + eapply NodesDisjointForSameStart_permutation; eauto.
    + split.
      * eapply NodesCoverRemaining_permutation; eauto.
      * eapply NodesExcludeChosen_permutation; eauto.
Qed.

Lemma frontier_split_push_single_pending_forms_frontier :
  forall ps n L R chosen chosen_len total slots hsize nd slots_out,
    FrontierPushPrefix slots hsize nd slots_out ->
    FrontierSplitState ps n L R chosen chosen_len total
      (nd :: nil) (sublist 0 hsize slots) ->
    FrontierState ps n L R chosen chosen_len total
      (sublist 0 (hsize + 1) slots_out).
Proof.
  intros ps n L R chosen chosen_len total slots hsize nd slots_out
    [Hlen Hperm] Hsplit.
  unfold FrontierSplitState in Hsplit.
  simpl in Hsplit.
  eapply FrontierState_permutation; eauto.
Qed.

Lemma frontier_split_push_left_keeps_right_pending :
  forall ps n L R chosen chosen_len total left right slots hsize slots_out,
    FrontierPushPrefix slots hsize left slots_out ->
    FrontierSplitState ps n L R chosen chosen_len total
      (left :: right :: nil) (sublist 0 hsize slots) ->
    FrontierSplitState ps n L R chosen chosen_len total
      (right :: nil) (sublist 0 (hsize + 1) slots_out).
Proof.
  intros ps n L R chosen chosen_len total left right slots hsize slots_out
    [Hlen Hperm] Hsplit.
  unfold FrontierSplitState in *.
  simpl in Hsplit |- *.
  eapply (FrontierState_permutation ps n L R chosen chosen_len total
      (left :: right :: sublist 0 hsize slots)
      (right :: sublist 0 (hsize + 1) slots_out)).
  - eapply Permutation_trans with
      (l' := right :: left :: sublist 0 hsize slots).
    + change
        (Permutation
          (left :: [right] ++ sublist 0 hsize slots)
          ([right] ++ left :: sublist 0 hsize slots)).
      apply Permutation_middle.
    + eapply Permutation_cons.
      * reflexivity.
      * exact Hperm.
  - exact Hsplit.
Qed.

Lemma PrefixArrayPrefix_entry_abs_bound :
  forall l pref upto i,
    PrefixArrayPrefix l pref upto ->
    (forall idx, 0 <= idx < upto -> -1000 <= Znth idx l 0 <= 1000) ->
    0 <= i <= upto ->
    -1000 * i <= Znth i pref 0 <= 1000 * i.
Proof.
  intros l pref upto i [Hpreflen [Hpref0 Hstep]] Hbound Hi.
  assert (Hmain :
    forall k,
      Z.of_nat k <= upto ->
      -1000 * Z.of_nat k <= Znth (Z.of_nat k) pref 0 <= 1000 * Z.of_nat k).
  {
    induction k as [|k IH].
    - intros _. cbn. rewrite Hpref0. lia.
    - intros Hk.
      assert (Hk_prev : Z.of_nat k <= upto) by lia.
      specialize (IH Hk_prev).
      assert (Hz_range : 0 <= Z.of_nat k < upto) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      rewrite Hstep by exact Hz_range.
      specialize (Hbound (Z.of_nat k) Hz_range).
      lia.
  }
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply Hmain.
  lia.
Qed.

Lemma PrefixArrayPrefix_functional :
  forall l pref1 pref2 upto,
    PrefixArrayPrefix l pref1 upto ->
    PrefixArrayPrefix l pref2 upto ->
    pref1 = pref2.
Proof.
  intros l pref1 pref2 upto
    [Hlen1 [Hzero1 Hstep1]]
    [Hlen2 [Hzero2 Hstep2]].
  apply (proj2 (list_eq_ext pref1 pref2 0)).
  split; [lia|].
  intros i Hi.
  assert (Hmain :
    forall k,
      Z.of_nat k <= upto ->
      Znth (Z.of_nat k) pref1 0 = Znth (Z.of_nat k) pref2 0).
  {
    induction k as [|k IH].
    - intros _. cbn. rewrite Hzero1, Hzero2. reflexivity.
    - intros Hk.
      assert (Hk_prev : Z.of_nat k <= upto) by lia.
      specialize (IH Hk_prev).
      assert (Hz_range : 0 <= Z.of_nat k < upto) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      rewrite Hstep1 by exact Hz_range.
      rewrite Hstep2 by exact Hz_range.
      now rewrite IH.
  }
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply Hmain.
  lia.
Qed.

Lemma PrefixSums_functional :
  forall l ps1 ps2,
    PrefixSums l ps1 ->
    PrefixSums l ps2 ->
    ps1 = ps2.
Proof.
  intros l ps1 ps2 Hps1 Hps2.
  rewrite PrefixSums_recurrence in *.
  eapply PrefixArrayPrefix_functional; eauto.
Qed.

Lemma PrefixSums_diff_int_bounds :
  forall l ps n i j,
    PrefixSums l ps ->
    Zlength l = n ->
    n <= 100000 ->
    (forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) ->
    0 <= i <= n ->
    0 <= j <= n ->
    -2147483648 <= Znth i ps 0 - Znth j ps 0 <= 2147483647.
Proof.
  intros l ps n i j Hpref Hlenn Hn Hbound Hi Hj.
  rewrite PrefixSums_recurrence in Hpref.
  rewrite Hlenn in Hpref.
  pose proof (PrefixArrayPrefix_entry_abs_bound l ps n i Hpref Hbound Hi)
    as Hi_bound.
  pose proof (PrefixArrayPrefix_entry_abs_bound l ps n j Hpref Hbound Hj)
    as Hj_bound.
  lia.
Qed.

Lemma ValidNodeFields_value_int_bound :
  forall l ps n L R value start lo hi best,
    PrefixSums l ps ->
    Zlength l = n ->
    n <= 100000 ->
    1 <= L ->
    (forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) ->
    ValidNodeFields ps n L R value start lo hi best ->
    -2147483648 <= value <= 2147483647.
Proof.
  intros l ps n L R value start lo hi best Hpref Hlen Hn HL Hbound Hvalid.
  unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
  cbn in Hvalid.
  destruct Hvalid as
    [Hps_len [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbest_hi [Hvalue _]]]]]]]]].
  rewrite Hvalue.
  eapply PrefixSums_diff_int_bounds; eauto; lia.
Qed.

Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.Classical_Prop.

Lemma valid_chord_value_int_bound :
  forall l ps n L R code,
    PrefixSums l ps ->
    Zlength l = n ->
    n <= 100000 ->
    (forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) ->
    ValidChordCode ps n L R code ->
    -2147483648 <= ChordValueOfCode ps n code <= 2147483647.
Proof.
  intros l ps n L R code Hpref Hlen Hn Hbound Hvalid.
  unfold ValidChordCode in Hvalid.
  destruct Hvalid as [_ [Hstart [Hstart_end [Hend _]]]].
  unfold ChordValueOfCode.
  eapply PrefixSums_diff_int_bounds; eauto.
  - lia.
  - lia.
Qed.

Lemma chord_values_sum_int64_bound :
  forall l ps n L R codes,
    PrefixSums l ps ->
    Zlength l = n ->
    n <= 100000 ->
    (forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) ->
    Forall (ValidChordCode ps n L R) codes ->
    (-2147483648) * Zlength codes <=
      sum (map (fun code => ChordValueOfCode ps n code) codes) <=
      2147483647 * Zlength codes.
Proof.
  intros l ps n L R codes Hpref Hlen Hn Hbound Hfor.
  induction Hfor as [|code codes Hcode Hfor IH].
  - unfold sum; simpl; nia.
  - unfold sum in IH |- *; simpl in *.
    pose proof (valid_chord_value_int_bound l ps n L R code Hpref Hlen Hn Hbound Hcode)
      as Hcode_bound.
    destruct Hcode_bound as [Hcode_lo Hcode_hi].
    destruct IH as [IH_lo IH_hi].
    assert (Hzlen_cons : Zlength (code :: codes) = Zlength codes + 1).
    { rewrite Zlength_cons; lia. }
    rewrite Hzlen_cons.
    split.
    + change (((-2147483648) * (Zlength codes + 1)) <=
         ChordValueOfCode ps n code +
         fold_right Z.add 0 (map (fun code : Z => ChordValueOfCode ps n code) codes)).
      replace ((-2147483648) * (Zlength codes + 1))
        with (((-2147483648) * Zlength codes) + (-2147483648)) by nia.
      rewrite Z.add_comm with (n := (-2147483648) * Zlength codes) (m := -2147483648).
      apply Z.add_le_mono; [exact Hcode_lo | exact IH_lo].
    + change (ChordValueOfCode ps n code +
         fold_right Z.add 0 (map (fun code : Z => ChordValueOfCode ps n code) codes) <=
         2147483647 * (Zlength codes + 1)).
      replace (2147483647 * (Zlength codes + 1))
        with ((2147483647 * Zlength codes) + 2147483647) by nia.
      rewrite Z.add_comm with (n := 2147483647 * Zlength codes) (m := 2147483647).
      apply Z.add_le_mono; [exact Hcode_hi | exact IH_hi].
Qed.

Lemma frontier_total_int64_bound :
  forall l ps n L R chosen chosen_len total nodes,
    PrefixSums l ps ->
    Zlength l = n ->
    n <= 100000 ->
    (forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) ->
    FrontierState ps n L R chosen chosen_len total nodes ->
    (-2147483648) * chosen_len <= total <= 2147483647 * chosen_len.
Proof.
  intros l ps n L R chosen chosen_len total nodes
    Hpref Hlen Hn Hbound Hfrontier.
  unfold FrontierState in Hfrontier.
  destruct Hfrontier as [Hcodes [Hsum _]].
  unfold ValidSongCodes in Hcodes.
  destruct Hcodes as [Hchosen_len [_ Hfor]].
  unfold SongCodesSum in Hsum.
  subst total.
  rewrite <- Hchosen_len.
  eapply chord_values_sum_int64_bound; eauto.
Qed.

Lemma frontier_state_top_node_valid :
  forall ps n L R chosen chosen_len total slots hsize,
    0 < hsize ->
    hsize <= Zlength slots ->
    FrontierState ps n L R chosen chosen_len total (sublist 0 hsize slots) ->
    ValidNodeFields ps n L R
      (heap_top_value slots) (heap_top_start slots)
      (heap_top_lo slots) (heap_top_hi slots) (heap_top_best slots).
Proof.
  intros ps n L R chosen chosen_len total slots hsize Hhsize Hhsize_len Hfrontier.
  unfold FrontierState in Hfrontier.
  destruct Hfrontier as [_ [_ [_ [Hfor _]]]].
  rewrite Forall_forall in Hfor.
  assert (Htop_in : In (heap_top_node slots) (sublist 0 hsize slots)).
  {
    unfold heap_top_node.
    rewrite <- (Znth_sublist0 default_node 0 hsize slots) by lia.
    apply nth_In with (d := default_node).
    apply Nat2Z.inj_lt.
    simpl.
    rewrite <- Zlength_correct.
    rewrite Zlength_sublist0 by lia.
    lia.
  }
  specialize (Hfor _ Htop_in).
  unfold ValidNodeFields.
  destruct (heap_top_node slots) as [[[[v s] lo] hi] best] eqn:Hnode.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best.
  rewrite Hnode.
  simpl in *.
  exact Hfor.
Qed.

Lemma frontier_state_nonempty_if_more_choices_remain :
  forall ps n L R k ans chosen chosen_len total slots hsize,
    SuperPianoAnswerByPrefix ps n L R k ans ->
    FrontierState ps n L R chosen chosen_len total (sublist 0 hsize slots) ->
    0 <= hsize ->
    hsize <= Zlength slots ->
    chosen_len < k ->
    0 < hsize.
Proof.
  intros ps n L R k ans chosen chosen_len total slots hsize
    Hanswer Hfrontier Hhsize_nonneg Hhsize_len Hmore.
  unfold SuperPianoAnswerByPrefix in Hanswer.
  unfold max_value_of_subset, max_object_of_subset in Hanswer.
  destruct Hanswer as [codes [[Hcodes_valid _] _]].
  unfold FrontierState in Hfrontier.
  destruct Hfrontier as [Hchosen_valid [_ [_ [_ [_ [Hcover _]]]]]].
  unfold ValidSongCodes in Hchosen_valid.
  destruct Hchosen_valid as [Hchosen_len [Hchosen_nodup _]].
  unfold ValidSongCodes in Hcodes_valid.
  destruct Hcodes_valid as [Hcodes_len [Hcodes_nodup Hcodes_forall]].
  assert (Hexists_missing : exists code, In code codes /\ ~ In code chosen).
  {
    destruct (classic (exists code, In code codes /\ ~ In code chosen))
      as [Hmiss | Hno_miss]; [exact Hmiss|].
    exfalso.
    assert (Hincl : incl codes chosen).
    {
      intros code Hcode_in.
      destruct (classic (In code chosen)) as [Hin | Hnotin]; [exact Hin|].
      exfalso.
      apply Hno_miss.
      exists code; split; assumption.
    }
    pose proof (NoDup_incl_length Hcodes_nodup Hincl) as Hlen_le.
    apply Nat2Z.inj_le in Hlen_le.
    rewrite <- !Zlength_correct in Hlen_le.
    lia.
  }
  destruct Hexists_missing as [code [Hcode_in Hcode_notin]].
  rewrite Forall_forall in Hcodes_forall.
  pose proof (Hcodes_forall code Hcode_in) as Hcode_valid.
  destruct (Hcover code Hcode_valid Hcode_notin) as [nd [Hnd_in _]].
  destruct (@In_nth Node (sublist 0 hsize slots) nd default_node Hnd_in)
    as [idx [Hidx _]].
  apply Nat2Z.inj_lt in Hidx.
  rewrite <- Zlength_correct in Hidx.
  rewrite Zlength_sublist in Hidx by lia.
  lia.
Qed.

Lemma sum_map_remove_split :
  forall (f : Z -> Z) pre x post,
    sum (map f (pre ++ x :: post)) =
    f x + sum (map f (pre ++ post)).
Proof.
  intros f pre x post.
  rewrite !map_app.
  rewrite !sum_app.
  simpl.
  lia.
Qed.

Lemma Forall_remove_split :
  forall (P : Z -> Prop) pre x post,
    Forall P (pre ++ x :: post) ->
    Forall P (pre ++ post).
Proof.
  intros P pre x post Hfor.
  rewrite Forall_forall in *.
  intros y Hy.
  apply Hfor.
  rewrite in_app_iff in *.
  destruct Hy as [Hy | Hy]; [left; exact Hy|].
  right; simpl; right; exact Hy.
Qed.

Lemma topk_sum_by_dominance :
  forall (valid : Z -> Prop) (f : Z -> Z) chosen codes,
    NoDup chosen ->
    NoDup codes ->
    Zlength codes = Zlength chosen ->
    Forall valid codes ->
    (forall picked rest,
      In picked chosen ->
      In rest codes ->
      valid rest ->
      ~ In rest chosen ->
      f rest <= f picked) ->
    sum (map f codes) <= sum (map f chosen).
Proof.
  intros valid f chosen.
  induction chosen as [|picked chosen IH]; intros codes Hnodup_chosen Hnodup_codes
    Hlen Hfor Hdom.
  - destruct codes as [|code codes].
    + simpl; lia.
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      unfold Z.succ in Hlen.
      pose proof (Zlength_nonneg codes).
      lia.
  - inversion Hnodup_chosen as [|? ? Hpicked_notin Hnodup_tail]; subst.
    destruct (classic (In picked codes)) as [Hpicked_in_codes | Hpicked_notin_codes].
    + destruct (in_split _ _ Hpicked_in_codes) as [pre [post Hcodes_eq]].
      subst codes.
      rewrite sum_map_remove_split.
      simpl.
      apply Z.add_le_mono_l.
      assert (Hnodup_codes' : NoDup (pre ++ post)).
      { eapply NoDup_remove_1; exact Hnodup_codes. }
      assert (Hfor_codes' : Forall valid (pre ++ post)).
      { eapply Forall_remove_split; exact Hfor. }
      assert (Hlen_codes' : Zlength (pre ++ post) = Zlength chosen).
      {
        repeat rewrite Zlength_app in Hlen.
        repeat rewrite Zlength_cons in Hlen.
        unfold Z.succ in Hlen.
        rewrite Zlength_app.
        lia.
      }
      eapply IH; eauto.
      intros picked' rest Hpicked'_in Hrest_in Hrest_valid Hrest_notin_tail.
      apply Hdom.
      * simpl; right; exact Hpicked'_in.
      * rewrite in_app_iff in *.
        destruct Hrest_in as [Hin | Hin].
        -- left; exact Hin.
        -- right; simpl; right; exact Hin.
      * exact Hrest_valid.
      * intros Hrest_in_full.
        simpl in Hrest_in_full.
        destruct Hrest_in_full as [Hrest_eq_picked | Hrest_in_tail].
        -- subst rest.
           eapply NoDup_remove_2; eauto.
        -- apply Hrest_notin_tail; exact Hrest_in_tail.
    + assert (Hexists_outside_tail :
        exists rest, In rest codes /\ ~ In rest chosen).
      {
        destruct (classic (exists rest, In rest codes /\ ~ In rest chosen))
          as [Hmiss | Hno_miss]; [exact Hmiss|].
        exfalso.
        assert (Hincl_tail : incl codes chosen).
        {
          intros code Hcode_in.
          destruct (classic (In code chosen)) as [Hin | Hnotin]; [exact Hin|].
          exfalso; apply Hno_miss.
          exists code; split; assumption.
        }
        pose proof (NoDup_incl_length Hnodup_codes Hincl_tail) as Hlen_le.
        apply Nat2Z.inj_le in Hlen_le.
        rewrite <- !Zlength_correct in Hlen_le.
        rewrite Zlength_cons in Hlen.
        lia.
      }
      destruct Hexists_outside_tail as [rest [Hrest_in_codes Hrest_notin_tail]].
      destruct (in_split _ _ Hrest_in_codes) as [pre [post Hcodes_eq]].
      subst codes.
      rewrite sum_map_remove_split.
      simpl.
      assert (Hrest_valid : valid rest).
      {
        rewrite Forall_forall in Hfor.
        apply Hfor.
        rewrite in_app_iff.
        right; simpl; left; reflexivity.
      }
      assert (Hrest_le_picked : f rest <= f picked).
      {
        apply Hdom.
        - simpl; left; reflexivity.
        - rewrite in_app_iff.
          right; simpl; left; reflexivity.
        - exact Hrest_valid.
        - intros Hrest_in_full.
          simpl in Hrest_in_full.
          destruct Hrest_in_full as [Hrest_eq_picked | Hrest_in_tail].
          + subst rest; contradiction.
          + apply Hrest_notin_tail; exact Hrest_in_tail.
      }
      assert (Hnodup_codes' : NoDup (pre ++ post)).
      { eapply NoDup_remove_1; exact Hnodup_codes. }
      assert (Hfor_codes' : Forall valid (pre ++ post)).
      { eapply Forall_remove_split; exact Hfor. }
      assert (Hlen_codes' : Zlength (pre ++ post) = Zlength chosen).
      {
        repeat rewrite Zlength_app in Hlen.
        repeat rewrite Zlength_cons in Hlen.
        unfold Z.succ in Hlen.
        rewrite Zlength_app.
        lia.
      }
      pose proof (IH (pre ++ post) Hnodup_tail Hnodup_codes'
        Hlen_codes' Hfor_codes') as IHsum.
      assert (Hdom_tail :
        forall picked' rest',
          In picked' chosen ->
          In rest' (pre ++ post) ->
          valid rest' ->
          ~ In rest' chosen ->
          f rest' <= f picked').
      {
        intros picked' rest' Hpicked'_in Hrest'_in Hrest'_valid Hrest'_notin_tail.
        apply Hdom.
        - simpl; right; exact Hpicked'_in.
        - rewrite in_app_iff in *.
          destruct Hrest'_in as [Hin | Hin].
          + left; exact Hin.
          + right; simpl; right; exact Hin.
        - exact Hrest'_valid.
        - intros Hrest'_in_full.
          simpl in Hrest'_in_full.
          destruct Hrest'_in_full as [Hrest'_eq_picked | Hrest'_in_tail].
          + subst rest'.
            apply Hpicked_notin_codes.
            rewrite in_app_iff in *.
            destruct Hrest'_in as [Hin | Hin].
            * left; exact Hin.
            * right; simpl; right; exact Hin.
          + apply Hrest'_notin_tail; exact Hrest'_in_tail.
      }
      specialize (IHsum Hdom_tail).
      lia.
Qed.

Lemma frontier_state_complete_implies_answer :
  forall ps n L R k chosen total nodes,
    FrontierState ps n L R chosen k total nodes ->
    SuperPianoAnswerByPrefix ps n L R k total.
Proof.
  intros ps n L R k chosen total nodes Hfrontier.
  unfold FrontierState in Hfrontier.
  destruct Hfrontier as [Hchosen_valid [Hsum [Hdom _]]].
  unfold SuperPianoAnswerByPrefix.
  unfold max_value_of_subset, max_object_of_subset.
  exists chosen.
  split.
  - split.
    + exact Hchosen_valid.
    + intros codes Hcodes_valid.
      unfold ValidSongCodes in Hchosen_valid.
      destruct Hchosen_valid as [Hchosen_len [Hchosen_nodup Hchosen_forall]].
      unfold ValidSongCodes in Hcodes_valid.
      destruct Hcodes_valid as [Hcodes_len [Hcodes_nodup Hcodes_forall]].
      unfold SongCodesSum in Hsum.
      subst total.
      eapply topk_sum_by_dominance with
        (valid := ValidChordCode ps n L R)
        (chosen := chosen)
        (codes := codes).
      * exact Hchosen_nodup.
      * exact Hcodes_nodup.
      * lia.
      * exact Hcodes_forall.
      * intros picked rest Hpicked_in Hrest_in Hrest_valid Hrest_notin.
        eapply Hdom; eauto.
  - unfold SongCodesSum in Hsum.
    symmetry; exact Hsum.
Qed.

Lemma nth_Znth :
  forall {A : Type} (d : A) (l : list A) (n : nat),
    (n < length l)%nat ->
    nth n l d = Znth (Z.of_nat n) l d.
Proof.
  intros A d l.
  induction l as [| a l IH]; intros [| n] Hlt; simpl in *; try lia.
  - rewrite Znth0_cons. reflexivity.
  - rewrite Znth_cons by lia.
    replace (Z.pos (Pos.of_succ_nat n) - 1) with (Z.of_nat n) by lia.
    rewrite IH by lia.
    reflexivity.
Qed.

Lemma in_sublist0_Znth :
  forall {A : Type} (d : A) (hi : Z) (l : list A) (x : A),
    0 <= hi <= Zlength l ->
    In x (sublist 0 hi l) ->
    exists i,
      0 <= i < hi /\
      Znth i l d = x.
Proof.
  intros A d hi l x Hrange Hin.
  destruct (In_nth (sublist 0 hi l) x d Hin) as [n [Hnlt Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite sublist_length in Hnlt by lia.
    lia.
  - rewrite <- Hnth.
    rewrite nth_Znth by exact Hnlt.
    assert (0 <= Z.of_nat n < hi) as Hi by (rewrite sublist_length in Hnlt by lia; lia).
    rewrite Znth_sublist0 by exact Hi.
    reflexivity.
Qed.

Lemma chord_code_eta :
  forall n code,
    0 <= n ->
    code = ChordCode n (CodeStart n code) (CodeEnd n code).
Proof.
  intros n code Hn.
  unfold ChordCode, CodeStart, CodeEnd.
  rewrite (Z.div_mod code (n + 1)) at 1 by lia.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Lemma chord_code_eq_of_start_end :
  forall n code start finish,
    0 <= n ->
    CodeStart n code = start ->
    CodeEnd n code = finish ->
    code = ChordCode n start finish.
Proof.
  intros n code start finish Hn Hstart Hend.
  rewrite (chord_code_eta n code Hn).
  now rewrite Hstart, Hend.
Qed.

Lemma node_eq_dec :
  forall nd1 nd2 : Node,
    {nd1 = nd2} + {nd1 <> nd2}.
Proof.
  repeat decide equality; apply Z.eq_dec.
Qed.

Lemma chord_code_start_end :
  forall n start finish,
    0 <= n ->
    0 <= finish <= n ->
    CodeStart n (ChordCode n start finish) = start /\
    CodeEnd n (ChordCode n start finish) = finish.
Proof.
  intros n start finish Hn Hfinish.
  unfold CodeStart, CodeEnd, ChordCode.
  split.
  - symmetry.
    apply Z.div_unique with (r := finish).
    + left. lia.
    + ring.
  - symmetry.
    apply Z.mod_unique with (q := start).
    + left. lia.
    + ring.
Qed.

Lemma chord_value_of_chord_code :
  forall ps n start finish,
    0 <= n ->
    0 <= finish <= n ->
    ChordValueOfCode ps n (ChordCode n start finish) =
      Znth finish ps 0 - Znth (start - 1) ps 0.
Proof.
  intros ps n start finish Hn Hfinish.
  unfold ChordValueOfCode.
  destruct (chord_code_start_end n start finish Hn Hfinish) as [Hstart Hend].
  rewrite Hstart, Hend.
  reflexivity.
Qed.

Lemma heap_top_node_fields_eq :
  forall slots value start lo hi best,
    value = heap_top_value slots ->
    start = heap_top_start slots ->
    lo = heap_top_lo slots ->
    hi = heap_top_hi slots ->
    best = heap_top_best slots ->
    heap_top_node slots = (value, start, lo, hi, best).
Proof.
  intros slots value start lo hi best Hvalue Hstart Hlo Hhi Hbest.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best in *.
  unfold heap_top_node in *.
  destruct (Znth 0 slots default_node) as [[[[v s] lo0] hi0] best0] eqn:Hz.
  cbn in *.
  subst.
  reflexivity.
Qed.

Lemma valid_node_fields_chord_valid :
  forall ps n L R value start lo hi best,
    1 <= L ->
    ValidNodeFields ps n L R value start lo hi best ->
    ValidChordCode ps n L R (ChordCode n start best).
Proof.
  intros ps n L R value start lo hi best HL Hvalid.
  unfold ValidNodeFields in *; rewrite ValidNode_unfold in *; unfold ValidChordCode in *.
  cbn in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi _]]]]]]]].
  destruct (chord_code_start_end n start best ltac:(lia) ltac:(lia))
    as [Hcode_start Hcode_end].
  repeat split.
  - exact Hlen.
  - rewrite Hcode_start. lia.
  - rewrite Hcode_start, Hcode_end. lia.
  - rewrite Hcode_end. lia.
  - rewrite Hcode_start, Hcode_end. lia.
  - rewrite Hcode_start, Hcode_end. lia.
Qed.

Lemma valid_node_fields_covers_best :
  forall ps n L R value start lo hi best,
    1 <= L ->
    ValidNodeFields ps n L R value start lo hi best ->
    NodeCoversCode n (value, start, lo, hi, best) (ChordCode n start best).
Proof.
  intros ps n L R value start lo hi best HL Hvalid.
  unfold ValidNodeFields in *; rewrite ValidNode_unfold in *; unfold NodeCoversCode in *.
  cbn in *.
  destruct Hvalid as
      [_ [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi _]]]]]]]].
  destruct (chord_code_start_end n start best ltac:(lia) ltac:(lia))
    as [Hcode_start Hcode_end].
  split.
  - exact Hcode_start.
  - rewrite Hcode_end. lia.
Qed.

Lemma valid_node_fields_code_value :
  forall ps n L R value start lo hi best,
    1 <= L ->
    ValidNodeFields ps n L R value start lo hi best ->
    ChordValueOfCode ps n (ChordCode n start best) = value.
Proof.
  intros ps n L R value start lo hi best HL Hvalid.
  unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
  cbn in Hvalid.
  destruct Hvalid as
      [_ [Hstart1 [Hstartn [HloL [_ [Hhin [Hlobest [Hbesthi [Hvalue _]]]]]]]]].
  rewrite chord_value_of_chord_code by lia.
  symmetry.
  exact Hvalue.
Qed.

Lemma node_covers_code_value_le :
  forall ps n L R nd code,
    ValidNode ps n L R nd ->
    NodeCoversCode n nd code ->
    ChordValueOfCode ps n code <= node_value nd.
Proof.
  intros ps n L R [[[[value start] lo] hi] best] code Hvalid Hcover.
  rewrite ValidNode_unfold in *; unfold NodeCoversCode in *.
  simpl in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi [Hvalue Hmax]]]]]]]]].
  destruct Hcover as [Hcode_start Hcode_range].
  unfold ChordValueOfCode.
  rewrite Hcode_start.
  apply Hmax.
  exact Hcode_range.
Qed.

Lemma node_heap_state_sublist_bound :
  forall slots size nd,
    0 < size -> NodeHeapState slots size ->
    In nd (sublist 0 size slots) -> node_value nd <= heap_top_value slots.
Proof.
  intros slots size nd Hsize [_ Hheap] Hin. destruct Hheap as [Hempty | [p [[Hp Hmax] Heq]]].
  - rewrite Hempty in Hin. contradiction.
  - specialize (Hmax nd Hin). lia.
Qed.


Lemma in_old_of_rest_perm :
  forall {A : Type} (top : A) rest old x,
    Permutation (top :: rest) old ->
    In x rest ->
    In x old.
Proof.
  intros A top rest old x Hperm Hin.
  eapply Permutation_in.
  - exact Hperm.
  - now right.
Qed.

Lemma in_rest_of_old_perm_neq :
  forall {A : Type} (top : A) rest old x,
    Permutation (top :: rest) old ->
    In x old ->
    x <> top ->
    In x rest.
Proof.
  intros A top rest old x Hperm Hin Hneq.
  assert (In x (top :: rest)) as Hin'.
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hin.
  }
  simpl in Hin'.
  destruct Hin' as [Heq | Hin_rest].
  - exfalso. apply Hneq. exact (eq_sym Heq).
  - exact Hin_rest.
Qed.

Lemma top_not_in_rest_of_perm :
  forall {A : Type} (top : A) rest old,
    Permutation (top :: rest) old ->
    NoDup old ->
    ~ In top rest.
Proof.
  intros A top rest old Hperm Hnodup.
  assert (NoDup (top :: rest)) as H by
      (apply (Permutation_NoDup (Permutation_sym Hperm)); exact Hnodup).
  inversion H; subst.
  exact H2.
Qed.

Lemma rest_nodup_of_perm :
  forall {A : Type} (top : A) rest old,
    Permutation (top :: rest) old ->
    NoDup old ->
    NoDup rest.
Proof.
  intros A top rest old Hperm Hnodup.
  assert (NoDup (top :: rest)) as H by
      (apply (Permutation_NoDup (Permutation_sym Hperm)); exact Hnodup).
  inversion H; subst.
  exact H3.
Qed.

Lemma disjoint_closed_no_overlap :
  forall lo1 hi1 lo2 hi2 x,
    DisjointClosed lo1 hi1 lo2 hi2 ->
    lo1 <= x <= hi1 ->
    lo2 <= x <= hi2 ->
    False.
Proof.
  intros lo1 hi1 lo2 hi2 x Hdisj Hx1 Hx2.
  unfold DisjointClosed in Hdisj.
  lia.
Qed.

Lemma valid_node_fields_left_child :
  forall ps n L R value start lo hi best retval,
    ValidNodeFields ps n L R value start lo hi best ->
    RangeArgmax ps lo (best - 1) retval ->
    lo <= best - 1 ->
    ValidNodeFields ps n L R
      (Znth retval ps 0 - Znth (start - 1) ps 0)
      start lo (best - 1) retval.
Proof.
  intros ps n L R value start lo hi best retval Hvalid Harg Hnonempty.
  unfold ValidNodeFields in *; rewrite ValidNode_unfold in *; rewrite RangeArgmax_unfold in *.
  cbn in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi [_ Hmax_old]]]]]]]]].
  try rewrite RangeArgmax_unfold in Harg.
  destruct Harg as [Hret_hi [Hret_best Hmax]].
  repeat split;
    [ exact Hlen
    | exact Hstart1
    | exact Hstartn
    | exact HloL
    | exact Hnonempty
    | lia
    | exact Hret_hi
    | exact Hret_best
    | intros finish Hfinish;
      assert (Znth finish ps 0 <= Znth retval ps 0) as Hle by (apply Hmax; lia);
      lia ].
Qed.

Lemma valid_node_fields_right_child :
  forall ps n L R value start lo hi best retval,
    ValidNodeFields ps n L R value start lo hi best ->
    RangeArgmax ps (best + 1) hi retval ->
    ValidNodeFields ps n L R
      (Znth retval ps 0 - Znth (start - 1) ps 0)
      start (best + 1) hi retval.
Proof.
  intros ps n L R value start lo hi best retval Hvalid Harg.
  unfold ValidNodeFields in *; rewrite ValidNode_unfold in *; rewrite RangeArgmax_unfold in *.
  cbn in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi [_ _]]]]]]]]].
  try rewrite RangeArgmax_unfold in Harg.
  destruct Harg as [Hret_hi [Hret_best Hmax]].
  repeat split;
    [ exact Hlen
    | exact Hstart1
    | exact Hstartn
    | lia
    | lia
    | exact Hhin
    | exact Hret_hi
    | exact Hret_best
    | intros finish Hfinish;
      assert (Znth finish ps 0 <= Znth retval ps 0) as Hle by (apply Hmax; lia);
      lia ].
Qed.

Lemma frontier_pop_to_split_both_children :
  forall ps n L R chosen t total slots size slots_out
         value start lo hi best retval retval_2,
    1 <= L ->
    0 < size ->
    FrontierState ps n L R chosen t total (sublist 0 size slots) ->
    FrontierPopTop slots size slots_out ->
    NodeHeapState slots size ->
    ValidNodeFields ps n L R value start lo hi best ->
    value = heap_top_value slots ->
    start = heap_top_start slots ->
    lo = heap_top_lo slots ->
    hi = heap_top_hi slots ->
    best = heap_top_best slots ->
    RangeArgmax ps lo (best - 1) retval ->
    lo <= best - 1 ->
    RangeArgmax ps (best + 1) hi retval_2 ->
    best + 1 <= hi ->
    FrontierSplitState ps n L R
      (ChordCode n start best :: chosen) (t + 1) (total + value)
      (mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start lo (best - 1) retval ::
       mkNode (Znth retval_2 ps 0 - Znth (start - 1) ps 0) start (best + 1) hi retval_2 ::
       nil)
      (sublist 0 (size - 1) slots_out).
Proof.
  intros ps n L R chosen t total slots size slots_out
         value start lo hi best retval retval_2
         HL Hsize Hstate Hpop Hheap Hvalid Hvalue Hstart Hlo Hhi Hbest
         Hleft Hleft_nonempty Hright Hright_nonempty.
  set (top := (value, start, lo, hi, best)).
  set (left_node :=
         mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start lo (best - 1) retval).
  set (right_node :=
         mkNode (Znth retval_2 ps 0 - Znth (start - 1) ps 0) start (best + 1) hi retval_2).
  set (old_nodes := sublist 0 size slots).
  set (rest := sublist 0 (size - 1) slots_out).
  pose proof (heap_top_node_fields_eq slots value start lo hi best Hvalue Hstart Hlo Hhi Hbest)
    as Htop_eq.
  pose proof (valid_node_fields_covers_best ps n L R value start lo hi best HL Hvalid)
    as Htop_cover.
  pose proof (valid_node_fields_code_value ps n L R value start lo hi best HL Hvalid)
    as Hchosen_value.
  assert (Hleft_valid :
            ValidNodeFields ps n L R
              (Znth retval ps 0 - Znth (start - 1) ps 0)
              start lo (best - 1) retval).
  { eapply valid_node_fields_left_child; eauto. }
  assert (Hright_valid :
            ValidNodeFields ps n L R
              (Znth retval_2 ps 0 - Znth (start - 1) ps 0)
              start (best + 1) hi retval_2).
  { eapply valid_node_fields_right_child; eauto. }
  assert (0 <= best <= n) as Hbest_bounds.
  {
    unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
    cbn in Hvalid.
    destruct Hvalid as
        [_ [Hstart1 [Hstartn [HloL0 [_ [Hhin0 [Hlobest0 [Hbesthi0 _]]]]]]]].
    lia.
  }
  destruct (chord_code_start_end n start best ltac:(lia) Hbest_bounds)
    as [Hchosen_start Hchosen_end].
  unfold FrontierSplitState.
  unfold FrontierState in *.
  destruct Hstate as [Hsong [Hsum [Hdom [Hnodes_valid [Hnodes_disj [Hcover Hexclude]]]]]].
  destruct Hsong as [Hchosen_len [Hchosen_nodup Hchosen_forall]].
  destruct Hnodes_disj as [Hold_nodup Hold_disj].
  rewrite Forall_forall in Hnodes_valid.
  rewrite Forall_forall in Hchosen_forall.
  unfold FrontierPopTop, FrontierPopPrefix in Hpop.
  destruct Hpop as [_ [Hin_top_old Hperm]].
  rewrite Htop_eq in Hperm.
  assert (In top old_nodes) as Hin_top.
  {
    subst top old_nodes.
    rewrite <- Htop_eq.
    exact Hin_top_old.
  }
  assert (NoDup rest) as Hrest_nodup.
  {
    subst rest old_nodes.
    eapply rest_nodup_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  assert (~ In top rest) as Htop_notin_rest.
  {
    subst rest old_nodes.
    eapply top_not_in_rest_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  repeat split.
  - rewrite Zlength_correct in Hchosen_len |- *.
    simpl in *.
    lia.
  - apply NoDup_cons.
    + intro Hin.
      specialize (Hexclude top (ChordCode n start best) Hin_top Htop_cover).
      contradiction.
    + exact Hchosen_nodup.
  - constructor.
    + eapply valid_node_fields_chord_valid; eauto.
    + apply Forall_forall.
      intros x Hinx.
      apply Hchosen_forall.
      exact Hinx.
  - unfold SongCodesSum in *.
    simpl.
    rewrite Hchosen_value, Hsum.
    lia.
  - unfold ChosenDominatesRemaining in Hdom |- *.
    intros picked code Hpicked Hcode_valid Hcode_notin.
    simpl in Hpicked.
    destruct Hpicked as [Hpicked | Hpicked].
    + subst picked.
      assert (~ In code chosen) as Hcode_notin_old.
      {
        intro Hin.
        apply Hcode_notin.
        right.
        exact Hin.
      }
      destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
      assert (ValidNode ps n L R nd) as Hnd_valid by (apply Hnodes_valid; exact Hnd_old).
      assert (ChordValueOfCode ps n code <= node_value nd) as Hcode_le_nd.
      { eapply node_covers_code_value_le; eauto. }
      assert (node_value nd <= value) as Hnd_le_top.
      {
        rewrite Hvalue.
        eapply node_heap_state_sublist_bound; eauto.
      }
      lia.
    + eapply Hdom; eauto.
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
  - constructor.
    + exact Hleft_valid.
    + constructor.
      * exact Hright_valid.
      * apply Forall_forall.
        intros nd Hnd_rest.
        apply Hnodes_valid.
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
  - constructor.
    + intro Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * unfold left_node, right_node, mkNode in Heq.
        inversion Heq; lia.
      * assert (In left_node old_nodes) as Hleft_old.
        {
          subst left_node rest old_nodes.
          eapply in_old_of_rest_perm; eauto.
        }
        assert (top <> left_node) as Hneq.
        {
          intro Heq.
          subst top left_node.
          unfold mkNode in Heq.
          inversion Heq; lia.
        }
        specialize (Hold_disj top left_node Hin_top Hleft_old Hneq eq_refl).
        subst top left_node.
        unfold mkNode in *.
        cbn in *.
        try rewrite RangeArgmax_unfold in Hleft.
        destruct Hleft as [Hret_hi [Hret_best Hmax]].
        exfalso.
        eapply disjoint_closed_no_overlap with (x := retval).
        -- exact Hold_disj.
        -- lia.
        -- lia.
    + constructor.
      * intro Hin.
        assert (In right_node old_nodes) as Hright_old.
        {
          subst right_node rest old_nodes.
          eapply in_old_of_rest_perm; eauto.
        }
        assert (top <> right_node) as Hneq.
        {
          intro Heq.
          subst top right_node.
          unfold mkNode in Heq.
          inversion Heq; lia.
        }
        specialize (Hold_disj top right_node Hin_top Hright_old Hneq eq_refl).
        subst top right_node.
        unfold mkNode in *.
        cbn in *.
        try rewrite RangeArgmax_unfold in Hright.
        destruct Hright as [Hret_hi [Hret_best Hmax]].
        exfalso.
        eapply disjoint_closed_no_overlap with (x := retval_2).
        -- exact Hold_disj.
        -- lia.
        -- lia.
      * exact Hrest_nodup.
  - intros nd1 nd2 Hnd1 Hnd2 Hneq Hsame.
    simpl in Hnd1, Hnd2.
    destruct Hnd1 as [Hnd1 | [Hnd1 | Hnd1]];
    destruct Hnd2 as [Hnd2 | [Hnd2 | Hnd2]].
    + subst nd1 nd2. contradiction.
    + subst nd1 nd2. cbn in *. unfold DisjointClosed. lia.
    + subst nd1.
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd2) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd2 rest.
        exact Hnd2.
      }
      specialize (Hold_disj top nd2 Hin_top Hnd2_old Hneq_top).
      subst top left_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj Hsame).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + subst nd1 nd2. cbn in *. unfold DisjointClosed. lia.
    + subst nd1 nd2. contradiction.
    + subst nd1.
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd2) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd2 rest.
        exact Hnd2.
      }
      specialize (Hold_disj top nd2 Hin_top Hnd2_old Hneq_top).
      subst top right_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj Hsame).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + subst nd2.
      assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd1) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd1 rest.
        exact Hnd1.
      }
      specialize (Hold_disj top nd1 Hin_top Hnd1_old Hneq_top).
      subst top left_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj (eq_sym Hsame)).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + subst nd2.
      assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd1) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd1 rest.
        exact Hnd1.
      }
      specialize (Hold_disj top nd1 Hin_top Hnd1_old Hneq_top).
      subst top right_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj (eq_sym Hsame)).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      eapply Hold_disj; eauto.
  - unfold NodesCoverRemaining in Hcover |- *.
    intros code Hcode_valid Hcode_notin.
    assert (~ In code chosen) as Hcode_notin_old.
    {
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
    }
    destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
    destruct (node_eq_dec nd top) as [Htop | Hneq_top].
    + subst nd top.
      destruct Hnd_cover as [Hcode_start Hcode_range].
      cbn in Hcode_start, Hcode_range.
      assert (code <> ChordCode n start best) as Hcode_neq_top.
      {
        intro Heq.
        apply Hcode_notin.
        left.
        exact (eq_sym Heq).
      }
      assert (CodeEnd n code <> best) as Hend_neq.
      {
        intro Hend.
        apply Hcode_neq_top.
        eapply chord_code_eq_of_start_end; eauto; lia.
      }
      assert (CodeEnd n code <= best - 1 \/ best + 1 <= CodeEnd n code) as Hbranch by lia.
      destruct Hbranch as [Hbranch | Hbranch].
      * exists left_node.
        split.
        -- simpl. left. reflexivity.
        -- subst left_node.
           unfold NodeCoversCode, mkNode.
           cbn.
           split; [exact Hcode_start | lia].
      * exists right_node.
        split.
        -- simpl. right. left. reflexivity.
        -- subst right_node.
           unfold NodeCoversCode, mkNode.
           cbn.
           split; [exact Hcode_start | lia].
    + assert (In nd rest) as Hnd_rest.
      {
        subst top rest old_nodes.
        eapply in_rest_of_old_perm_neq; eauto.
      }
      exists nd.
      split.
      * simpl. right. right. exact Hnd_rest.
      * exact Hnd_cover.
  - unfold NodesExcludeChosen in Hexclude |- *.
    intros nd code Hnd_new Hnd_cover Hcode_in.
    simpl in Hnd_new, Hcode_in.
    destruct Hnd_new as [Hnd_new | [Hnd_new | Hnd_new]].
    + destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        subst nd.
        unfold left_node, NodeCoversCode, mkNode in Hnd_cover.
        cbn in Hnd_cover.
        destruct Hnd_cover as [_ Hrange].
        rewrite Hchosen_end in Hrange.
        lia.
      * exfalso.
        assert (Htop_covers_code : NodeCoversCode n top code).
        {
          subst top.
          subst nd.
          unfold left_node, NodeCoversCode, mkNode in Hnd_cover |- *.
          unfold node_start, node_lo, node_hi in Hnd_cover |- *.
          cbn in *.
          destruct Hnd_cover as [Hcode_start [Hrange_lo Hrange_hi]].
          assert (Hbest_le_hi : best <= hi).
          {
            unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
            lia.
          }
          split; [exact Hcode_start | split; [exact Hrange_lo | lia]].
        }
        exact (Hexclude top code Hin_top Htop_covers_code Hin_old).
    + destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        subst nd.
        unfold right_node, NodeCoversCode, mkNode in Hnd_cover.
        cbn in Hnd_cover.
        destruct Hnd_cover as [_ Hrange].
        rewrite Hchosen_end in Hrange.
        lia.
      * exfalso.
        assert (Htop_covers_code : NodeCoversCode n top code).
        {
          subst top.
          subst nd.
          unfold right_node, NodeCoversCode, mkNode in Hnd_cover |- *.
          unfold node_start, node_lo, node_hi in Hnd_cover |- *.
          cbn in *.
          destruct Hnd_cover as [Hcode_start [Hrange_lo Hrange_hi]].
          split; [exact Hcode_start | split; [lia | exact Hrange_hi]].
        }
        exact (Hexclude top code Hin_top Htop_covers_code Hin_old).
    + assert (In nd old_nodes) as Hnd_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        destruct Hnd_cover as [Hcode_start Hcode_range].
        assert (top <> nd) as Hneq_top.
        {
          intro Heq'.
          apply Htop_notin_rest.
          subst nd rest.
          exact Hnd_new.
        }
        assert (node_start top = node_start nd) as Hsame_start.
        {
          subst top.
          cbn.
          rewrite <- Hchosen_start.
          exact Hcode_start.
        }
        specialize (Hold_disj top nd Hin_top Hnd_old Hneq_top Hsame_start).
        subst top.
        rewrite Hchosen_end in Hcode_range.
        assert (Htop_best_range : lo <= best <= hi).
        {
          unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
          lia.
        }
        eapply disjoint_closed_no_overlap with (x := best) in Hold_disj;
          [contradiction| exact Htop_best_range | exact Hcode_range].
      * eapply Hexclude; eauto.
Qed.

Lemma frontier_pop_to_split_left_only :
  forall ps n L R chosen t total slots size slots_out
         value start lo hi best retval,
    1 <= L ->
    0 < size ->
    FrontierState ps n L R chosen t total (sublist 0 size slots) ->
    FrontierPopTop slots size slots_out ->
    NodeHeapState slots size ->
    ValidNodeFields ps n L R value start lo hi best ->
    value = heap_top_value slots ->
    start = heap_top_start slots ->
    lo = heap_top_lo slots ->
    hi = heap_top_hi slots ->
    best = heap_top_best slots ->
    RangeArgmax ps lo (best - 1) retval ->
    lo <= best - 1 ->
    hi <= best ->
    FrontierSplitState ps n L R
      (ChordCode n start best :: chosen) (t + 1) (total + value)
      (mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start lo (best - 1) retval ::
       nil)
      (sublist 0 (size - 1) slots_out).
Proof.
  intros ps n L R chosen t total slots size slots_out
         value start lo hi best retval
         HL Hsize Hstate Hpop Hheap Hvalid Hvalue Hstart Hlo Hhi Hbest
         Hleft Hleft_nonempty Hhi_best.
  set (top := (value, start, lo, hi, best)).
  set (left_node :=
         mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start lo (best - 1) retval).
  set (old_nodes := sublist 0 size slots).
  set (rest := sublist 0 (size - 1) slots_out).
  pose proof (heap_top_node_fields_eq slots value start lo hi best Hvalue Hstart Hlo Hhi Hbest)
    as Htop_eq.
  pose proof (valid_node_fields_covers_best ps n L R value start lo hi best HL Hvalid)
    as Htop_cover.
  pose proof (valid_node_fields_code_value ps n L R value start lo hi best HL Hvalid)
    as Hchosen_value.
  assert (Hleft_valid :
            ValidNodeFields ps n L R
              (Znth retval ps 0 - Znth (start - 1) ps 0)
              start lo (best - 1) retval).
  { eapply valid_node_fields_left_child; eauto. }
  assert (0 <= best <= n) as Hbest_bounds.
  {
    unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
    cbn in Hvalid.
    destruct Hvalid as
        [_ [Hstart1 [Hstartn [HloL0 [_ [Hhin0 [Hlobest0 [Hbesthi0 _]]]]]]]].
    lia.
  }
  destruct (chord_code_start_end n start best ltac:(lia) Hbest_bounds)
    as [Hchosen_start Hchosen_end].
  unfold FrontierSplitState.
  unfold FrontierState in *.
  destruct Hstate as [Hsong [Hsum [Hdom [Hnodes_valid [Hnodes_disj [Hcover Hexclude]]]]]].
  destruct Hsong as [Hchosen_len [Hchosen_nodup Hchosen_forall]].
  destruct Hnodes_disj as [Hold_nodup Hold_disj].
  rewrite Forall_forall in Hnodes_valid.
  rewrite Forall_forall in Hchosen_forall.
  unfold FrontierPopTop, FrontierPopPrefix in Hpop.
  destruct Hpop as [_ [Hin_top_old Hperm]].
  rewrite Htop_eq in Hperm.
  assert (In top old_nodes) as Hin_top.
  {
    subst top old_nodes.
    rewrite <- Htop_eq.
    exact Hin_top_old.
  }
  assert (NoDup rest) as Hrest_nodup.
  {
    subst rest old_nodes.
    eapply rest_nodup_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  assert (~ In top rest) as Htop_notin_rest.
  {
    subst rest old_nodes.
    eapply top_not_in_rest_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  repeat split.
  - rewrite Zlength_correct in Hchosen_len |- *.
    simpl in *.
    lia.
  - apply NoDup_cons.
    + intro Hin.
      specialize (Hexclude top (ChordCode n start best) Hin_top Htop_cover).
      contradiction.
    + exact Hchosen_nodup.
  - constructor.
    + eapply valid_node_fields_chord_valid; eauto.
    + apply Forall_forall.
      intros x Hinx.
      apply Hchosen_forall.
      exact Hinx.
  - unfold SongCodesSum in *.
    simpl.
    rewrite Hchosen_value, Hsum.
    lia.
  - unfold ChosenDominatesRemaining in Hdom |- *.
    intros picked code Hpicked Hcode_valid Hcode_notin.
    simpl in Hpicked.
    destruct Hpicked as [Hpicked | Hpicked].
    + subst picked.
      assert (~ In code chosen) as Hcode_notin_old.
      {
        intro Hin.
        apply Hcode_notin.
        right.
        exact Hin.
      }
      destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
      assert (ValidNode ps n L R nd) as Hnd_valid by (apply Hnodes_valid; exact Hnd_old).
      assert (ChordValueOfCode ps n code <= node_value nd) as Hcode_le_nd.
      { eapply node_covers_code_value_le; eauto. }
      assert (node_value nd <= value) as Hnd_le_top.
      {
        rewrite Hvalue.
        eapply node_heap_state_sublist_bound; eauto.
      }
      lia.
    + eapply Hdom; eauto.
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
  - constructor.
    + exact Hleft_valid.
    + apply Forall_forall.
      intros nd Hnd_rest.
      apply Hnodes_valid.
      subst rest old_nodes.
      eapply in_old_of_rest_perm; eauto.
  - constructor.
    + intro Hin.
      assert (In left_node old_nodes) as Hleft_old.
      {
        subst left_node rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> left_node) as Hneq.
      {
        intro Heq.
        assert (Hbest_le_hi : best <= hi).
        {
          unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
          lia.
        }
        subst top left_node.
        unfold mkNode in Heq.
        inversion Heq; lia.
      }
      specialize (Hold_disj top left_node Hin_top Hleft_old Hneq eq_refl).
      subst top left_node.
      unfold mkNode in *.
      cbn in *.
      try rewrite RangeArgmax_unfold in Hleft.
      destruct Hleft as [Hret_hi [Hret_best Hmax]].
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      exfalso.
      eapply disjoint_closed_no_overlap with (x := retval).
      * exact Hold_disj.
      * lia.
      * lia.
    + exact Hrest_nodup.
  - intros nd1 nd2 Hnd1 Hnd2 Hneq Hsame.
    simpl in Hnd1, Hnd2.
    destruct Hnd1 as [Hnd1 | Hnd1];
    destruct Hnd2 as [Hnd2 | Hnd2].
    + subst nd1 nd2. contradiction.
    + subst nd1.
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd2) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd2 rest.
        exact Hnd2.
      }
      specialize (Hold_disj top nd2 Hin_top Hnd2_old Hneq_top).
      subst top left_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj Hsame).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + subst nd2.
      assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd1) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd1 rest.
        exact Hnd1.
      }
      specialize (Hold_disj top nd1 Hin_top Hnd1_old Hneq_top).
      subst top left_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj (eq_sym Hsame)).
      unfold DisjointClosed in *.
      cbn in *.
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
        lia.
      }
      lia.
    + assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      eapply Hold_disj; eauto.
  - unfold NodesCoverRemaining in Hcover |- *.
    intros code Hcode_valid Hcode_notin.
    assert (~ In code chosen) as Hcode_notin_old.
    {
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
    }
    destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
    destruct (node_eq_dec nd top) as [Htop | Hneq_top].
    + subst nd top.
      destruct Hnd_cover as [Hcode_start Hcode_range].
      cbn in Hcode_start, Hcode_range.
      assert (code <> ChordCode n start best) as Hcode_neq_top.
      {
        intro Heq.
        apply Hcode_notin.
        left.
        exact (eq_sym Heq).
      }
      assert (CodeEnd n code <> best) as Hend_neq.
      {
        intro Hend.
        apply Hcode_neq_top.
        eapply chord_code_eq_of_start_end; eauto; lia.
      }
      exists left_node.
      split.
      * simpl. left. reflexivity.
      * subst left_node.
        unfold NodeCoversCode, mkNode.
        cbn.
        split; [exact Hcode_start | lia].
    + assert (In nd rest) as Hnd_rest.
      {
        subst top rest old_nodes.
        eapply in_rest_of_old_perm_neq; eauto.
      }
      exists nd.
      split.
      * simpl. right. exact Hnd_rest.
      * exact Hnd_cover.
  - unfold NodesExcludeChosen in Hexclude |- *.
    intros nd code Hnd_new Hnd_cover Hcode_in.
    simpl in Hnd_new, Hcode_in.
    destruct Hnd_new as [Hnd_new | Hnd_new].
    + destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        subst nd.
        unfold left_node, NodeCoversCode, mkNode in Hnd_cover.
        unfold node_start, node_lo, node_hi in Hnd_cover.
        cbn in Hnd_cover.
        destruct Hnd_cover as [_ [Hrange_lo Hrange_hi]].
        rewrite Hchosen_end in Hrange_hi.
        lia.
      * exfalso.
        assert (Htop_covers_code : NodeCoversCode n top code).
        {
          subst top.
          subst nd.
          unfold left_node, NodeCoversCode, mkNode in Hnd_cover |- *.
          unfold node_start, node_lo, node_hi in Hnd_cover |- *.
          cbn in *.
          destruct Hnd_cover as [Hcode_start [Hrange_lo Hrange_hi]].
          assert (Hbest_le_hi : best <= hi).
          {
            unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
            lia.
          }
          split; [exact Hcode_start | split; [exact Hrange_lo | lia]].
        }
        exact (Hexclude top code Hin_top Htop_covers_code Hin_old).
    + assert (In nd old_nodes) as Hnd_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        destruct Hnd_cover as [Hcode_start Hcode_range].
        assert (top <> nd) as Hneq_top.
        {
          intro Heq'.
          apply Htop_notin_rest.
          subst nd rest.
          exact Hnd_new.
        }
        assert (node_start top = node_start nd) as Hsame_start.
        {
          subst top.
          cbn.
          rewrite <- Hchosen_start.
          exact Hcode_start.
        }
        specialize (Hold_disj top nd Hin_top Hnd_old Hneq_top Hsame_start).
        subst top.
        rewrite Hchosen_end in Hcode_range.
        assert (Htop_best_range : lo <= best <= hi).
        {
          unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
          lia.
        }
        eapply disjoint_closed_no_overlap with (x := best) in Hold_disj;
          [contradiction| exact Htop_best_range | exact Hcode_range].
      * eapply Hexclude; eauto.
Qed.

Lemma frontier_pop_to_split_right_only :
  forall ps n L R chosen t total slots size slots_out
         value start lo hi best retval,
    1 <= L ->
    0 < size ->
    FrontierState ps n L R chosen t total (sublist 0 size slots) ->
    FrontierPopTop slots size slots_out ->
    NodeHeapState slots size ->
    ValidNodeFields ps n L R value start lo hi best ->
    value = heap_top_value slots ->
    start = heap_top_start slots ->
    lo = heap_top_lo slots ->
    hi = heap_top_hi slots ->
    best = heap_top_best slots ->
    RangeArgmax ps (best + 1) hi retval ->
    best <= lo ->
    FrontierSplitState ps n L R
      (ChordCode n start best :: chosen) (t + 1) (total + value)
      (mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start (best + 1) hi retval ::
       nil)
      (sublist 0 (size - 1) slots_out).
Proof.
  intros ps n L R chosen t total slots size slots_out
         value start lo hi best retval
         HL Hsize Hstate Hpop Hheap Hvalid Hvalue Hstart Hlo Hhi Hbest
         Hright Hbest_lo.
  set (top := (value, start, lo, hi, best)).
  set (right_node :=
         mkNode (Znth retval ps 0 - Znth (start - 1) ps 0) start (best + 1) hi retval).
  set (old_nodes := sublist 0 size slots).
  set (rest := sublist 0 (size - 1) slots_out).
  pose proof (heap_top_node_fields_eq slots value start lo hi best Hvalue Hstart Hlo Hhi Hbest)
    as Htop_eq.
  pose proof (valid_node_fields_covers_best ps n L R value start lo hi best HL Hvalid)
    as Htop_cover.
  pose proof (valid_node_fields_code_value ps n L R value start lo hi best HL Hvalid)
    as Hchosen_value.
  assert (Hright_valid :
            ValidNodeFields ps n L R
              (Znth retval ps 0 - Znth (start - 1) ps 0)
              start (best + 1) hi retval).
  { eapply valid_node_fields_right_child; eauto. }
  assert (0 <= best <= n) as Hbest_bounds.
  {
    unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
    cbn in Hvalid.
    destruct Hvalid as
        [_ [Hstart1 [Hstartn [HloL0 [_ [Hhin0 [Hlobest0 [Hbesthi0 _]]]]]]]].
    lia.
  }
  destruct (chord_code_start_end n start best ltac:(lia) Hbest_bounds)
    as [Hchosen_start Hchosen_end].
  unfold FrontierSplitState.
  unfold FrontierState in *.
  destruct Hstate as [Hsong [Hsum [Hdom [Hnodes_valid [Hnodes_disj [Hcover Hexclude]]]]]].
  destruct Hsong as [Hchosen_len [Hchosen_nodup Hchosen_forall]].
  destruct Hnodes_disj as [Hold_nodup Hold_disj].
  rewrite Forall_forall in Hnodes_valid.
  rewrite Forall_forall in Hchosen_forall.
  unfold FrontierPopTop, FrontierPopPrefix in Hpop.
  destruct Hpop as [_ [Hin_top_old Hperm]].
  rewrite Htop_eq in Hperm.
  assert (In top old_nodes) as Hin_top.
  {
    subst top old_nodes.
    rewrite <- Htop_eq.
    exact Hin_top_old.
  }
  assert (NoDup rest) as Hrest_nodup.
  {
    subst rest old_nodes.
    eapply rest_nodup_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  assert (~ In top rest) as Htop_notin_rest.
  {
    subst rest old_nodes.
    eapply top_not_in_rest_of_perm.
    - exact Hperm.
    - exact Hold_nodup.
  }
  assert (Hlo_best : lo <= best).
  {
    unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
    lia.
  }
  repeat split.
  - rewrite Zlength_correct in Hchosen_len |- *.
    simpl in *.
    lia.
  - apply NoDup_cons.
    + intro Hin.
      specialize (Hexclude top (ChordCode n start best) Hin_top Htop_cover).
      contradiction.
    + exact Hchosen_nodup.
  - constructor.
    + eapply valid_node_fields_chord_valid; eauto.
    + apply Forall_forall.
      intros x Hinx.
      apply Hchosen_forall.
      exact Hinx.
  - unfold SongCodesSum in *.
    simpl.
    rewrite Hchosen_value, Hsum.
    lia.
  - unfold ChosenDominatesRemaining in Hdom |- *.
    intros picked code Hpicked Hcode_valid Hcode_notin.
    simpl in Hpicked.
    destruct Hpicked as [Hpicked | Hpicked].
    + subst picked.
      assert (~ In code chosen) as Hcode_notin_old.
      {
        intro Hin.
        apply Hcode_notin.
        right.
        exact Hin.
      }
      destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
      assert (ValidNode ps n L R nd) as Hnd_valid by (apply Hnodes_valid; exact Hnd_old).
      assert (ChordValueOfCode ps n code <= node_value nd) as Hcode_le_nd.
      { eapply node_covers_code_value_le; eauto. }
      assert (node_value nd <= value) as Hnd_le_top.
      {
        rewrite Hvalue.
        eapply node_heap_state_sublist_bound; eauto.
      }
      lia.
    + eapply Hdom; eauto.
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
  - constructor.
    + exact Hright_valid.
    + apply Forall_forall.
      intros nd Hnd_rest.
      apply Hnodes_valid.
      subst rest old_nodes.
      eapply in_old_of_rest_perm; eauto.
  - constructor.
    + intro Hin.
      assert (In right_node old_nodes) as Hright_old.
      {
        subst right_node rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> right_node) as Hneq.
      {
        intro Heq.
        subst top right_node.
        unfold mkNode in Heq.
        inversion Heq; lia.
      }
      specialize (Hold_disj top right_node Hin_top Hright_old Hneq eq_refl).
      subst top right_node.
      unfold mkNode in *.
      cbn in *.
      try rewrite RangeArgmax_unfold in Hright.
      destruct Hright as [Hret_hi [Hret_best Hmax]].
      exfalso.
      eapply disjoint_closed_no_overlap with (x := retval).
      * exact Hold_disj.
      * lia.
      * lia.
    + exact Hrest_nodup.
  - intros nd1 nd2 Hnd1 Hnd2 Hneq Hsame.
    simpl in Hnd1, Hnd2.
    destruct Hnd1 as [Hnd1 | Hnd1];
    destruct Hnd2 as [Hnd2 | Hnd2].
    + subst nd1 nd2. contradiction.
    + subst nd1.
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd2) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd2 rest.
        exact Hnd2.
      }
      specialize (Hold_disj top nd2 Hin_top Hnd2_old Hneq_top).
      subst top right_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj Hsame).
      unfold DisjointClosed in *.
      cbn in *.
      lia.
    + subst nd2.
      assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (top <> nd1) as Hneq_top.
      {
        intro Heq.
        apply Htop_notin_rest.
        subst nd1 rest.
        exact Hnd1.
      }
      specialize (Hold_disj top nd1 Hin_top Hnd1_old Hneq_top).
      subst top right_node.
      unfold mkNode in *.
      cbn in Hsame.
      specialize (Hold_disj (eq_sym Hsame)).
      unfold DisjointClosed in *.
      cbn in *.
      lia.
    + assert (In nd1 old_nodes) as Hnd1_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      assert (In nd2 old_nodes) as Hnd2_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      eapply Hold_disj; eauto.
  - unfold NodesCoverRemaining in Hcover |- *.
    intros code Hcode_valid Hcode_notin.
    assert (~ In code chosen) as Hcode_notin_old.
    {
      intro Hin.
      apply Hcode_notin.
      right.
      exact Hin.
    }
    destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_old Hnd_cover]].
    destruct (node_eq_dec nd top) as [Htop | Hneq_top].
    + subst nd top.
      destruct Hnd_cover as [Hcode_start Hcode_range].
      cbn in Hcode_start, Hcode_range.
      assert (code <> ChordCode n start best) as Hcode_neq_top.
      {
        intro Heq.
        apply Hcode_notin.
        left.
        exact (eq_sym Heq).
      }
      assert (CodeEnd n code <> best) as Hend_neq.
      {
        intro Hend.
        apply Hcode_neq_top.
        eapply chord_code_eq_of_start_end; eauto; lia.
      }
      exists right_node.
      split.
      * simpl. left. reflexivity.
      * subst right_node.
        unfold NodeCoversCode, mkNode.
        cbn.
        split; [exact Hcode_start | lia].
    + assert (In nd rest) as Hnd_rest.
      {
        subst top rest old_nodes.
        eapply in_rest_of_old_perm_neq; eauto.
      }
      exists nd.
      split.
      * simpl. right. exact Hnd_rest.
      * exact Hnd_cover.
  - unfold NodesExcludeChosen in Hexclude |- *.
    intros nd code Hnd_new Hnd_cover Hcode_in.
    simpl in Hnd_new, Hcode_in.
    destruct Hnd_new as [Hnd_new | Hnd_new].
    + destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        subst nd.
        unfold right_node, NodeCoversCode, mkNode in Hnd_cover.
        unfold node_start, node_lo, node_hi in Hnd_cover.
        cbn in Hnd_cover.
        destruct Hnd_cover as [_ [Hrange_lo Hrange_hi]].
        rewrite Hchosen_end in Hrange_lo.
        lia.
      * exfalso.
        assert (Htop_covers_code : NodeCoversCode n top code).
        {
          subst top.
          subst nd.
          unfold right_node, NodeCoversCode, mkNode in Hnd_cover |- *.
          unfold node_start, node_lo, node_hi in Hnd_cover |- *.
          cbn in *.
          destruct Hnd_cover as [Hcode_start [Hrange_lo Hrange_hi]].
          split; [exact Hcode_start | split; [lia | exact Hrange_hi]].
        }
        exact (Hexclude top code Hin_top Htop_covers_code Hin_old).
    + assert (In nd old_nodes) as Hnd_old.
      {
        subst rest old_nodes.
        eapply in_old_of_rest_perm; eauto.
      }
      destruct Hcode_in as [Heq | Hin_old].
      * subst code.
        destruct Hnd_cover as [Hcode_start Hcode_range].
        assert (top <> nd) as Hneq_top.
        {
          intro Heq'.
          apply Htop_notin_rest.
          subst nd rest.
          exact Hnd_new.
        }
        assert (node_start top = node_start nd) as Hsame_start.
        {
          subst top.
          cbn.
          rewrite <- Hchosen_start.
          exact Hcode_start.
        }
        specialize (Hold_disj top nd Hin_top Hnd_old Hneq_top Hsame_start).
        subst top.
        rewrite Hchosen_end in Hcode_range.
        assert (Htop_best_range : lo <= best <= hi).
        {
          unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
          lia.
        }
        eapply disjoint_closed_no_overlap with (x := best) in Hold_disj;
          [contradiction| exact Htop_best_range | exact Hcode_range].
      * eapply Hexclude; eauto.
Qed.

Lemma frontier_top_value_dominates_remaining :
  forall ps n L R chosen chosen_len total slots size code,
    0 < size ->
    NodeHeapState slots size ->
    FrontierState ps n L R chosen chosen_len total (sublist 0 size slots) ->
    ValidChordCode ps n L R code ->
    ~ In code chosen ->
    ChordValueOfCode ps n code <= heap_top_value slots.
Proof.
  intros ps n L R chosen chosen_len total slots size code
    Hsize Hheap Hfrontier Hcode Hnotin.
  unfold FrontierState in Hfrontier.
  destruct Hfrontier as [_ [_ [_ [Hfor [_ [Hcover _]]]]]].
  destruct (Hcover code Hcode Hnotin) as [nd [Hnd_in Hnd_covers]].
  rewrite Forall_forall in Hfor.
  pose proof (Hfor nd Hnd_in) as Hnd_valid.
  pose proof (node_covers_code_value_le ps n L R nd code Hnd_valid Hnd_covers)
    as Hcode_le_nd.
  pose proof (node_heap_state_sublist_bound slots size nd Hsize Hheap Hnd_in)
    as Hnd_le_top.
  lia.
Qed.

Lemma frontier_pop_to_split_singleton :
  forall ps n L R chosen t total slots size slots_out
         value start lo hi best,
    1 <= L ->
    0 < size ->
    FrontierState ps n L R chosen t total (sublist 0 size slots) ->
    FrontierPopTop slots size slots_out ->
    NodeHeapState slots size ->
    ValidNodeFields ps n L R value start lo hi best ->
    value = heap_top_value slots ->
    start = heap_top_start slots ->
    lo = heap_top_lo slots ->
    hi = heap_top_hi slots ->
    best = heap_top_best slots ->
    lo = best ->
    best = hi ->
    FrontierSplitState ps n L R
      (ChordCode n start best :: chosen) (t + 1) (total + value)
      nil
      (sublist 0 (size - 1) slots_out).
Proof.
  intros ps n L R chosen t total slots size slots_out
         value start lo hi best
         HL Hsize Hstate Hpop Hheap Hvalid Hvalue Hstart Hlo Hhi Hbest
         Hlo_best Hbest_hi.
  pose proof (heap_top_node_fields_eq slots value start lo hi best Hvalue Hstart Hlo Hhi Hbest)
    as Htop_eq.
  pose proof (valid_node_fields_covers_best ps n L R value start lo hi best HL Hvalid)
    as Htop_cover.
  pose proof (valid_node_fields_code_value ps n L R value start lo hi best HL Hvalid)
    as Hchosen_value.
  assert (0 <= best <= n) as Hbest_bounds.
  {
    unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid.
    cbn in Hvalid.
    destruct Hvalid as
        [_ [Hstart1 [Hstartn [HloL0 [_ [Hhin0 [Hlobest0 [Hbesthi0 _]]]]]]]].
    lia.
  }
  destruct (chord_code_start_end n start best ltac:(lia) Hbest_bounds)
    as [Hchosen_start Hchosen_end].
  unfold FrontierSplitState.
  simpl.
  pose proof Hstate as Hstate_old.
  unfold FrontierState in Hstate |- *.
  destruct Hstate as [Hcodes [Hsum [Hdom [Hfor [Hdisjoint [Hcover Hexclude]]]]]].
  unfold FrontierPopTop, FrontierPopPrefix in Hpop.
  destruct Hpop as [_ [Htop_in Hperm]].
  rewrite Htop_eq in Hperm.
  repeat split.
  - unfold ValidSongCodes in Hcodes.
    destruct Hcodes as [Hchosen_len _].
    rewrite Zlength_cons. lia.
  - unfold ValidSongCodes in Hcodes.
    destruct Hcodes as [_ [Hnodup _]].
    constructor.
    + intro Hin.
      eapply (Hexclude (heap_top_node slots) (ChordCode n start best)).
      * exact Htop_in.
      * rewrite Htop_eq. exact Htop_cover.
      * exact Hin.
    + exact Hnodup.
  - unfold ValidSongCodes in Hcodes.
    destruct Hcodes as [_ [_ Hforall_codes]].
    constructor.
    + eapply valid_node_fields_chord_valid; eauto.
    + exact Hforall_codes.
  - unfold SongCodesSum in *.
    simpl.
    rewrite Hchosen_value.
    lia.
  - unfold ChosenDominatesRemaining in *.
    intros picked rest Hpicked Hrest_valid Hrest_notin_new.
    simpl in Hpicked.
    destruct Hpicked as [Hpicked_top | Hpicked_old].
    + subst picked.
      rewrite Hchosen_value.
      rewrite Hvalue.
      assert (Hrest_notin_old : ~ In rest chosen).
      {
        intro Hin_old.
        apply Hrest_notin_new.
        simpl; right; exact Hin_old.
      }
      eapply (frontier_top_value_dominates_remaining
        ps n L R chosen t total slots size rest); eauto.
    + apply Hdom; auto.
      intro Hin_old.
      apply Hrest_notin_new.
      simpl; right; exact Hin_old.
  - assert (Hfor_pop :
       Forall (ValidNode ps n L R)
         ((value, start, lo, hi, best) :: sublist 0 (size - 1) slots_out)).
    {
      eapply Forall_permutation.
      - apply Permutation_sym; exact Hperm.
      - exact Hfor.
    }
    inversion Hfor_pop; assumption.
  - assert (Hdisjoint_pop :
       NodesDisjointForSameStart
         ((value, start, lo, hi, best) :: sublist 0 (size - 1) slots_out)).
    {
      eapply NodesDisjointForSameStart_permutation.
      - apply Permutation_sym; exact Hperm.
      - exact Hdisjoint.
    }
    destruct Hdisjoint_pop as [Hnodup_pop Hdisj_pop].
    inversion Hnodup_pop as [|? ? Htop_notin_resid Hnodup_resid]; subst.
    exact Hnodup_resid.
  - assert (Hdisjoint_pop :
       NodesDisjointForSameStart
         ((value, start, lo, hi, best) :: sublist 0 (size - 1) slots_out)).
    {
      eapply NodesDisjointForSameStart_permutation.
      - apply Permutation_sym; exact Hperm.
      - exact Hdisjoint.
    }
    destruct Hdisjoint_pop as [_ Hdisj_pop].
    intros nd1 nd2 Hin1 Hin2 Hneq Hsame.
    eapply Hdisj_pop; eauto; simpl; right; assumption.
  - intros code Hcode_valid Hcode_notin_new.
    assert (Hcode_notin_old : ~ In code chosen).
    {
      intro Hin_old.
      apply Hcode_notin_new.
      simpl; right; exact Hin_old.
    }
    destruct (Hcover code Hcode_valid Hcode_notin_old) as [nd [Hnd_in_old Hnd_covers]].
    assert (Hnd_in_pop :
      In nd ((value, start, lo, hi, best) :: sublist 0 (size - 1) slots_out)).
    {
      eapply Permutation_in.
      - apply Permutation_sym; exact Hperm.
      - exact Hnd_in_old.
    }
    simpl in Hnd_in_pop.
    destruct Hnd_in_pop as [Hnd_top | Hnd_resid].
    + exfalso.
      subst nd.
      apply Hcode_notin_new.
      left.
      destruct Hnd_covers as [Hcode_start Hcode_range].
      cbn in Hcode_start, Hcode_range.
      assert (CodeEnd n code = best) by lia.
      symmetry.
      eapply chord_code_eq_of_start_end; eauto; lia.
    + exists nd; split; assumption.
  - intros nd code Hnd_in_resid Hnd_covers Hcode_in_new.
    simpl in Hcode_in_new.
    destruct Hcode_in_new as [Hcode_top | Hcode_in_old].
    + subst code.
      assert (Hdisjoint_pop :
        NodesDisjointForSameStart
          ((value, start, lo, hi, best) :: sublist 0 (size - 1) slots_out)).
      {
        eapply NodesDisjointForSameStart_permutation.
        - apply Permutation_sym; exact Hperm.
        - exact Hdisjoint.
      }
      destruct Hdisjoint_pop as [Hnodup_pop Hdisj_pop].
      assert ((value, start, lo, hi, best) <> nd) as Hneq_top.
      {
        inversion Hnodup_pop as [|? ? Hnotin _]; subst.
        intro Heq.
        apply Hnotin.
        rewrite Heq.
        exact Hnd_in_resid.
      }
      destruct Hnd_covers as [Hcover_start Hcover_range].
      assert (node_start (value, start, lo, hi, best) = node_start nd) as Hsame_start.
      {
        cbn.
        rewrite <- Hchosen_start.
        exact Hcover_start.
      }
      pose proof (Hdisj_pop (value, start, lo, hi, best) nd
        (or_introl eq_refl) (or_intror Hnd_in_resid)
        Hneq_top Hsame_start) as Hclosed_disjoint.
      rewrite Hchosen_end in Hcover_range.
      eapply disjoint_closed_no_overlap with (x := best) in Hclosed_disjoint;
        [contradiction| | exact Hcover_range].
      cbn.
      lia.
    + eapply Hexclude.
      * eapply Permutation_in.
        -- exact Hperm.
        -- simpl; right; exact Hnd_in_resid.
      * exact Hnd_covers.
      * exact Hcode_in_old.
Qed.

(** Sparse-table entries are maximizing positions, following the rmq interval
    contract and preserving the positions needed to split chord intervals. *)
Definition PianoSparseProgress (ps table : list Z) (n level upto : Z) : Prop :=
  forall row column,
    0 <= row -> 0 <= column < ST_LEVELS -> row + Power2 column <= n ->
    (column < level \/ column = level /\ row < upto) ->
    RangeArgmax ps row (row + Power2 column - 1)
      (Znth (row * ST_LEVELS + column) table 0).
Definition PianoSparseTable (ps table : list Z) (n : Z) : Prop :=
  forall row column,
    0 <= row -> 0 <= column < ST_LEVELS -> row + Power2 column <= n ->
    RangeArgmax ps row (row + Power2 column - 1)
      (Znth (row * ST_LEVELS + column) table 0).

Definition PianoSwap (slots : list Node) (a b : Z) : list Node :=
  replace_Znth b (Znth a slots default_node)
    (replace_Znth a (Znth b slots default_node) slots).

(** Node identities are preserved separately from the scalar priorities.
    Sift invariants reuse the priority_queue mathematical contract. *)
Definition PianoHeapPush (before current : list Node) (size child : Z) (nd : Node) : Prop :=
  FrontierPushPrefix before size nd current /\
  priority_queue_lib.PushLoopState
    (map node_value (sublist 0 size before) ++ [node_value nd])
    (map node_value (sublist 0 (size + 1) current)) size child (node_value nd).
Definition PianoHeapPop (before current : list Node) (size index : Z) : Prop :=
  FrontierPopTop before size current /\
  priority_queue_lib.PopLoopState
    (map node_value (sublist 0 size before))
    (map node_value (sublist 0 size current)) size index.
Definition PianoHeapSelected (current : list Node) (size index selected : Z) : Prop :=
  priority_queue_lib.PopSelectedChild (map node_value (sublist 0 (size + 1) current)) size index selected.
Definition PianoInitialPrefix (ps : list Z) (n L R upto : Z) (nodes : list Node) : Prop :=
  Forall (fun nd => ValidNode ps n L R nd /\
  1 <= node_start nd < upto /\ node_lo nd = node_start nd + L - 1 /\
  node_hi nd = Z.min n (node_start nd + R - 1)) nodes /\
  Permutation (map node_start nodes) (Zrange 1 upto).

Definition PianoNodes (vals starts los his bests : list Z) : list Node :=
  map (fun p => let '(v,(s,(l,(h,b)))) := p in mkNode v s l h b)
    (combine vals (combine starts (combine los (combine his bests)))).

Lemma piano_argmax_view ps lo hi best :
  RangeArgmax ps lo hi best <->
  (lo <= best <= hi /\ forall j, lo <= j <= hi -> Znth j ps 0 <= Znth best ps 0).
Proof. rewrite RangeArgmax_unfold. tauto. Qed.
Lemma piano_argmax_single ps i : RangeArgmax ps i i i.
Proof.
  apply piano_argmax_view. split; [lia|]. intros j Hj. assert (j = i) by lia. subst; lia.
Qed.
Lemma piano_argmax_join ps lo mid hi a b :
  lo <= mid -> mid <= hi ->
  RangeArgmax ps lo mid a -> RangeArgmax ps mid hi b ->
  Znth b ps 0 <= Znth a ps 0 -> RangeArgmax ps lo hi a.
Proof.
  intros Hlo Hhi Ha Hb Hle.
  apply piano_argmax_view in Ha, Hb. destruct Ha as [Ha Ham], Hb as [Hb Hbm].
  apply piano_argmax_view. split; [lia|]. intros j Hj.
  destruct (Z_le_dec j mid); [apply Ham; lia|]. specialize (Hbm j ltac:(lia)); lia.
Qed.
Lemma piano_argmax_union ps lo a_hi b_lo hi a b :
  b_lo <= a_hi + 1 -> lo <= b_lo -> a_hi <= hi ->
  RangeArgmax ps lo a_hi a -> RangeArgmax ps b_lo hi b ->
  RangeArgmax ps lo hi (if Z.geb (Znth a ps 0) (Znth b ps 0) then a else b).
Proof.
  intros Hcover Hlo Hhi Ha Hb.
  apply piano_argmax_view in Ha, Hb. destruct Ha as [Ha Ham], Hb as [Hb Hbm].
  destruct (Z.geb_spec (Znth a ps 0) (Znth b ps 0)); apply piano_argmax_view;
    split; try lia; intros j Hj; destruct (Z_le_dec j a_hi).
  - apply Ham; lia.
  - specialize (Hbm j ltac:(lia)); lia.
  - specialize (Ham j ltac:(lia)); lia.
  - apply Hbm; lia.
Qed.
Lemma piano_sparse_base_start ps table n : PianoSparseProgress ps table n 0 0.
Proof. intros row col Hr Hc Hn Hdone. unfold ST_LEVELS in *. lia. Qed.
Lemma piano_sparse_base_step ps table n i :
  Zlength table = n * ST_LEVELS -> 0 <= i < n ->
  PianoSparseProgress ps table n 0 i ->
  PianoSparseProgress ps (replace_Znth (i * ST_LEVELS) i table) n 0 (i + 1).
Proof.
  intros Hlen Hi Hprev row col Hr Hc Hn Hdone.
  assert (col = 0) by lia. subst col. unfold Power2 in Hn; simpl in Hn.
  unfold ST_LEVELS in *. destruct (Z.eq_dec row i) as [->|Hne].
  - rewrite Z.add_0_r, Znth_replace_Znth_Same by lia.
    replace (i + Power2 0 - 1) with i by (unfold Power2; simpl; lia).
    apply piano_argmax_single.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hprev; unfold ST_LEVELS, Power2 in *; simpl in *; lia.
Qed.
Lemma piano_sparse_base_complete ps table n :
  PianoSparseProgress ps table n 0 n -> PianoSparseProgress ps table n 1 0.
Proof.
  intros H row col Hr Hc Hn Hd. assert (col = 0) by lia; subst col.
  apply H; auto. right; split; auto. unfold Power2 in Hn; simpl in Hn; lia.
Qed.
Lemma piano_sparse_level_complete ps table n level i :
  1 <= level < ST_LEVELS -> i + Power2 level > n ->
  PianoSparseProgress ps table n level i -> PianoSparseProgress ps table n (level + 1) 0.
Proof.
  intros Hlevel Hi H row col Hr Hc Hn Hd. apply H; auto.
  destruct (Z_lt_ge_dec col level); [left; lia|]. right; split; [lia|].
  assert (col = level) by lia; subst col; lia.
Qed.
Lemma piano_sparse_complete ps table n :
  PianoSparseProgress ps table n ST_LEVELS 0 -> PianoSparseTable ps table n.
Proof. intros H row col Hr Hc Hn. apply H; auto; left; lia. Qed.
Lemma piano_sparse_read ps table n level i half width :
  1 <= level < ST_LEVELS -> half = Power2 (level - 1) -> width = Power2 level ->
  0 <= i -> i + width <= n ->
  PianoSparseProgress ps table n level i ->
  RangeArgmax ps i (i + half - 1) (Znth (i * ST_LEVELS + level - 1) table 0) /\
  RangeArgmax ps (i + half) (i + width - 1)
    (Znth ((i + half) * ST_LEVELS + level - 1) table 0).
Proof.
  intros Hl Hhalf Hw Hi Hn Hprog; subst half width.
  pose proof (Power2_pos (level - 1) ltac:(lia)).
  pose proof (Power2_sub1_double level ltac:(lia)). split.
  - replace (i * ST_LEVELS + level - 1) with (i * ST_LEVELS + (level - 1)) by lia.
    apply Hprog; try lia; left; lia.
  - replace ((i + Power2 (level - 1)) * ST_LEVELS + level - 1)
      with ((i + Power2 (level - 1)) * ST_LEVELS + (level - 1)) by lia.
    replace (i + Power2 level - 1)
      with (i + Power2 (level - 1) + Power2 (level - 1) - 1) by lia.
    apply Hprog; try lia; left; lia.
Qed.
Lemma piano_sparse_write ps table n level i best :
  Zlength table = n * ST_LEVELS ->
  0 <= level < ST_LEVELS -> 0 <= i -> i + Power2 level <= n ->
  PianoSparseProgress ps table n level i ->
  RangeArgmax ps i (i + Power2 level - 1) best ->
  PianoSparseProgress ps (replace_Znth (i * ST_LEVELS + level) best table) n level (i + 1).
Proof.
  intros Hlen Hl Hi Hn Hprev Hbest row col Hr Hc Hrange Hdone.
  pose proof (Power2_pos level ltac:(lia)).
  pose proof (Power2_pos col ltac:(lia)).
  destruct (Z.eq_dec (row * ST_LEVELS + col) (i * ST_LEVELS + level)) as [Heq|Hne].
  - assert (Hrc : row = i /\ col = level) by (unfold ST_LEVELS in *; lia).
    destruct Hrc as [-> ->]. rewrite Znth_replace_Znth_Same by (unfold ST_LEVELS in *; lia). exact Hbest.
  - rewrite Znth_replace_Znth_Diff by (unfold ST_LEVELS in *; lia).
    apply Hprev; auto. destruct Hdone as [Hlt|[Heq Hi']]; [left; auto|].
    right; split; auto. subst col. assert (row <> i) by (intro; subst; contradiction). lia.
Qed.
Lemma piano_sparse_query ps table n lo hi level width :
  0 <= lo <= hi -> hi < n -> 0 <= level < ST_LEVELS ->
  width = Power2 level -> 1 <= width -> width <= hi - lo + 1 -> hi - lo + 1 < 2 * width ->
  PianoSparseTable ps table n ->
  RangeArgmax ps lo hi
    (if Z.geb (Znth (Znth (lo * ST_LEVELS + level) table 0) ps 0)
              (Znth (Znth ((hi - width + 1) * ST_LEVELS + level) table 0) ps 0)
     then Znth (lo * ST_LEVELS + level) table 0
     else Znth ((hi - width + 1) * ST_LEVELS + level) table 0).
Proof.
  intros Hlo Hhi Hl Hw Hwpos Hwlen Hcover Htable.
  pose proof (Htable lo level ltac:(lia) Hl ltac:(lia)) as Ha.
  pose proof (Htable (hi - width + 1) level ltac:(lia) Hl ltac:(lia)) as Hb.
  rewrite <- Hw in Ha, Hb. replace (hi - width + 1 + width - 1) with hi in Hb by lia.
  eapply piano_argmax_union with (a_hi := lo + width - 1) (b_lo := hi - width + 1); eauto; lia.
Qed.

Lemma piano_Forall2_map {A B} (f : A -> B) ys xs :
  Forall2 (fun y x => y = f x) ys xs <-> ys = map f xs.
Proof.
  split.
  - induction 1; simpl; f_equal; assumption.
  - intros ->. induction xs; simpl; constructor; auto.
Qed.
Lemma piano_arrays_iff slots vals starts los his bests :
  NodeArrays slots vals starts los his bests <->
  vals = map node_value slots /\ starts = map node_start slots /\
  los = map node_lo slots /\ his = map node_hi slots /\ bests = map node_best slots.
Proof. unfold NodeArrays. rewrite !piano_Forall2_map. tauto. Qed.
Lemma piano_nodes_maps slots :
  PianoNodes (map node_value slots) (map node_start slots) (map node_lo slots)
    (map node_hi slots) (map node_best slots) = slots.
Proof.
  induction slots as [|[[[[v s] l] h] b] rest IH]; simpl; [reflexivity|].
  unfold PianoNodes in *; simpl in *; f_equal; exact IH.
Qed.
Lemma piano_nodes_eq slots vals starts los his bests :
  NodeArrays slots vals starts los his bests -> PianoNodes vals starts los his bests = slots.
Proof.
  rewrite piano_arrays_iff. intros (->&->&->&->&->). apply piano_nodes_maps.
Qed.
Lemma piano_map_replace {A B} (f : A -> B) i x xs :
  map f (replace_Znth i x xs) = replace_Znth i (f x) (map f xs).
Proof.
  unfold replace_Znth. generalize (Z.to_nat i) as k.
  induction xs as [|a xs IH]; intros k; destruct k; simpl; auto.
  rewrite IH; reflexivity.
Qed.
Lemma piano_map_sublist {A B} (f : A -> B) lo hi xs :
  map f (sublist lo hi xs) = sublist lo hi (map f xs).
Proof. unfold sublist. rewrite firstn_map, skipn_map; reflexivity. Qed.
Lemma piano_map_Znth {A B} (f : A -> B) i xs d :
  Znth i (map f xs) (f d) = f (Znth i xs d).
Proof. unfold Znth. apply map_nth. Qed.
Lemma piano_arrays_set slots vals starts los his bests i v s l h b :
  NodeArrays slots vals starts los his bests ->
  NodeArrays (replace_Znth i (mkNode v s l h b) slots)
    (replace_Znth i v vals) (replace_Znth i s starts) (replace_Znth i l los)
    (replace_Znth i h his) (replace_Znth i b bests).
Proof.
  rewrite !piano_arrays_iff. intros (->&->&->&->&->).
  rewrite !piano_map_replace. repeat split; reflexivity.
Qed.
Lemma piano_arrays_read slots vals starts los his bests i :
  NodeArrays slots vals starts los his bests ->
  Znth i vals 0 = node_value (Znth i slots default_node) /\
  Znth i starts 0 = node_start (Znth i slots default_node) /\
  Znth i los 0 = node_lo (Znth i slots default_node) /\
  Znth i his 0 = node_hi (Znth i slots default_node) /\
  Znth i bests 0 = node_best (Znth i slots default_node).
Proof.
  rewrite piano_arrays_iff. intros (->&->&->&->&->).
  repeat split; match goal with |- Znth ?j (map ?f ?xs) 0 = _ =>
    exact (piano_map_Znth f j xs default_node) end.
Qed.
Lemma piano_arrays_swap slots vals starts los his bests a b :
  NodeArrays slots vals starts los his bests ->
  NodeArrays (PianoSwap slots a b)
    (replace_Znth b (Znth a vals 0) (replace_Znth a (Znth b vals 0) vals))
    (replace_Znth b (Znth a starts 0) (replace_Znth a (Znth b starts 0) starts))
    (replace_Znth b (Znth a los 0) (replace_Znth a (Znth b los 0) los))
    (replace_Znth b (Znth a his 0) (replace_Znth a (Znth b his 0) his))
    (replace_Znth b (Znth a bests 0) (replace_Znth a (Znth b bests 0) bests)).
Proof.
  rewrite !piano_arrays_iff. intros (->&->&->&->&->).
  unfold PianoSwap. rewrite !piano_map_replace.
  repeat split; f_equal; try (match goal with |- Znth ?j (map ?f ?xs) 0 = _ => exact (piano_map_Znth f j xs default_node) end);
    f_equal; match goal with |- Znth ?j (map ?f ?xs) 0 = _ => exact (piano_map_Znth f j xs default_node) end.
Qed.

Lemma piano_argmax_left ps lo a_hi b_lo hi a b :
  b_lo <= a_hi + 1 -> lo <= b_lo -> a_hi <= hi ->
  RangeArgmax ps lo a_hi a -> RangeArgmax ps b_lo hi b ->
  Znth b ps 0 <= Znth a ps 0 -> RangeArgmax ps lo hi a.
Proof.
  intros Hcover Hl Hh Ha Hb Hle.
  pose proof (piano_argmax_union ps lo a_hi b_lo hi a b Hcover Hl Hh Ha Hb) as H.
  destruct (Z.geb_spec (Znth a ps 0) (Znth b ps 0)); [exact H|lia].
Qed.
Lemma piano_argmax_right ps lo a_hi b_lo hi a b :
  b_lo <= a_hi + 1 -> lo <= b_lo -> a_hi <= hi ->
  RangeArgmax ps lo a_hi a -> RangeArgmax ps b_lo hi b ->
  Znth a ps 0 < Znth b ps 0 -> RangeArgmax ps lo hi b.
Proof.
  intros Hcover Hl Hh Ha Hb Hlt.
  pose proof (piano_argmax_union ps lo a_hi b_lo hi a b Hcover Hl Hh Ha Hb) as H.
  destruct (Z.geb_spec (Znth a ps 0) (Znth b ps 0)); [lia|exact H].
Qed.
Lemma piano_power_bound level : 0 <= level <= 16 -> Power2 level <= 65536.
Proof.
  intros H. change (2 ^ level <= 2 ^ 16).
  apply Z.pow_le_mono_r; lia.
Qed.
Lemma piano_query_next_level n lo hi level width :
  n <= 100001 -> 0 <= lo <= hi -> hi < n -> 0 <= level ->
  width = Power2 level -> width * 2 <= hi - lo + 1 -> level + 1 < ST_LEVELS.
Proof.
  intros Hn Hlo Hhi Hl Hw Hstep. unfold ST_LEVELS.
  destruct (Z_lt_ge_dec level 16); [lia|].
  assert (65536 <= Power2 level).
  { change (2 ^ 16 <= 2 ^ level). apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

(** The priority_queue swap lemmas, generalized to node payloads. *)
Lemma piano_generic_replace_Znth_swap_form__push_sift_up {A : Type} :
  forall (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert
    (H0 :
      replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
      xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite
    (replace_Znth_nothing (A := A)
      (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace
    (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3)
    by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma piano_generic_permutation_swap_Znth_lt__push_sift_up {A : Type} :
  forall (l : list A) i j (d : A),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert
        (Hnat :
          (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
          Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite piano_generic_replace_Znth_swap_form__push_sift_up.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma piano_generic_replace_nth_comm_Z__push_sift_up {A : Type} :
  forall ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.
Lemma piano_generic_replace_Znth_comm__push_sift_up {A : Type} :
  forall (l : list A) i j (a b : A),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply piano_generic_replace_nth_comm_Z__push_sift_up.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma piano_generic_permutation_swap_Znth__push_sift_up {A : Type} :
  forall (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply piano_generic_permutation_swap_Znth_lt__push_sift_up.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite piano_generic_replace_Znth_comm__push_sift_up by lia.
      apply piano_generic_permutation_swap_Znth_lt__push_sift_up.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma piano_prefix_set {A} (xs : list A) n i v (d : A) :
  0 <= n <= Zlength xs -> 0 <= i < n ->
  sublist 0 n (replace_Znth i v xs) = replace_Znth i v (sublist 0 n xs).
Proof.
  intros Hn Hi. apply (proj2 (list_eq_ext _ _ d)); split.
  - rewrite Zlength_replace_Znth; rewrite !Zlength_sublist0 by (rewrite ?Zlength_replace_Znth; lia); reflexivity.
  - intros j Hj. rewrite Zlength_sublist0 in Hj by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_sublist0 by lia.
    destruct (Z.eq_dec i j) as [->|Hne].
    + rewrite !Znth_replace_Znth_Same by (rewrite ?Zlength_sublist0; lia). reflexivity.
    + rewrite !Znth_replace_Znth_Diff by (rewrite ?Zlength_sublist0; lia).
      rewrite Znth_sublist0 by lia; reflexivity.
Qed.
Lemma piano_prefix_set_outside {A} (xs : list A) n i v (d : A) :
  0 <= n <= i -> i < Zlength xs ->
  sublist 0 n (replace_Znth i v xs) = sublist 0 n xs.
Proof.
  intros Hn Hi. apply (proj2 (list_eq_ext _ _ d)); split.
  - rewrite !Zlength_sublist0 by (rewrite ?Zlength_replace_Znth; lia); reflexivity.
  - intros j Hj. rewrite Zlength_sublist0 in Hj by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite !Znth_sublist0 by lia. rewrite Znth_replace_Znth_Diff by lia; reflexivity.
Qed.
Lemma piano_prefix_append {A} (xs : list A) n v (d : A) :
  0 <= n < Zlength xs ->
  sublist 0 (n + 1) (replace_Znth n v xs) = sublist 0 n xs ++ [v].
Proof.
  intros Hn.
  rewrite (sublist_split 0 (n + 1) n) by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (piano_prefix_set_outside _ _ _ _ d) by lia.
  rewrite (sublist_single d) by (rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by lia; reflexivity.
Qed.
Lemma piano_swap_prefix (xs : list Node) n i j :
  0 <= n <= Zlength xs -> 0 <= i < n -> 0 <= j < n ->
  sublist 0 n (PianoSwap xs i j) = PianoSwap (sublist 0 n xs) i j.
Proof.
  intros Hn Hi Hj. unfold PianoSwap.
  rewrite !(piano_prefix_set _ _ _ _ default_node) by (rewrite ?Zlength_replace_Znth; lia).
  rewrite !Znth_sublist0 by lia. reflexivity.
Qed.
Lemma piano_swap_permutation (xs : list Node) i j :
  0 <= i < Zlength xs -> 0 <= j < Zlength xs -> Permutation xs (PianoSwap xs i j).
Proof. intros. apply piano_generic_permutation_swap_Znth__push_sift_up; auto. Qed.
Lemma piano_map_length {A B} (f : A -> B) xs : Zlength (map f xs) = Zlength xs.
Proof. rewrite !Zlength_correct, length_map; reflexivity. Qed.
Lemma piano_order_prefix slots size :
  0 <= size <= Zlength slots ->
  heap_ordered (map node_value (sublist 0 size slots)) size <->
  heap_ordered (map node_value slots) size.
Proof.
  intros Hsize. unfold heap_ordered. rewrite piano_map_sublist.
  split; intros H i Hi; pose proof (heap_parent_positive_bounds__push_sift_up i size ltac:(lia) ltac:(lia)) as Hp.
  - specialize (H i Hi). rewrite !Znth_sublist0 in H by lia. exact H.
  - rewrite !Znth_sublist0 by lia. apply H; auto.
Qed.
Lemma piano_heap_from_order slots size :
  0 <= size <= Zlength slots -> heap_ordered (map node_value slots) size -> NodeHeapState slots size.
Proof.
  intros Hsize Horder. split; [exact Horder|]. destruct (Z.eq_dec size 0) as [->|Hne].
  - left. apply Zsublist_nil; lia.
  - right. exists (heap_top_node slots). split; [split|reflexivity].
    + unfold heap_top_node.
      replace (Znth 0 slots default_node) with (Znth 0 (sublist 0 size slots) default_node)
        by (rewrite Znth_sublist0 by lia; reflexivity).
      apply Znth_In_Zlength. rewrite Zlength_sublist0 by lia; lia.
    + intros nd Hin.
      destruct (in_sublist0_Znth default_node size slots nd Hsize Hin) as [i [Hi Heq]]. subst nd.
      pose proof (heap_ordered_root_upper_bound__pop_initialization
        (map node_value slots) size i Horder Hi) as H.
      unfold heap_top_value, heap_top_node.
      change (Znth i (map node_value slots) (node_value default_node) <=
        Znth 0 (map node_value slots) (node_value default_node)) in H.
      rewrite !piano_map_Znth in H. exact H.
Qed.

Lemma piano_scalar_push_start :
  forall (base : list Z) (size x : Z),
    0 <= size -> Zlength base = size -> heap_ordered base size ->
    HeapProofFacts.PushLoopState (base ++ [x]) (base ++ [x]) size size x.
Proof.
  intros base size x Hsize_nonneg Hbase_length Hordered.
  unfold HeapProofFacts.PushLoopState.
  split; [exact Hsize_nonneg |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split; [exact Hsize_nonneg |].
      split; [lia |].
      split.
      * rewrite app_Znth2 by lia.
        rewrite Hbase_length.
        replace (size - size) with 0 by lia.
        reflexivity.
      * split.
        -- apply Permutation_refl.
        -- split.
           ++ unfold HeapProofFacts.HeapOrderExceptUp.
              split; [exact Hsize_nonneg |].
              split; [lia |].
              intros node [Hnode_positive [Hnode_bound Hnode_not_hole]].
              assert (Hnode_lt_size : node < size) by lia.
              assert (Hparent_nonneg : 0 <= heap_parent node).
              {
                unfold heap_parent.
                apply Z.quot_pos; lia.
              }
              assert (Hparent_lt_node : heap_parent node < node).
              {
                unfold heap_parent.
                apply Z.quot_lt_upper_bound; lia.
              }
              rewrite app_Znth1 by (rewrite Hbase_length; lia).
              rewrite app_Znth1 by (rewrite Hbase_length; lia).
              apply Hordered.
              lia.
           ++ unfold PushHoleChildrenPreserved.
              intros node [Hnode_positive [Hnode_bound Hparent_is_hole]].
              assert (Hparent_lt_node : heap_parent node < node).
              {
                unfold heap_parent.
                apply Z.quot_lt_upper_bound; lia.
              }
              lia.
Qed.

Lemma piano_push_start slots size nd :
  0 <= size < Zlength slots -> NodeHeapState slots size ->
  PianoHeapPush slots (replace_Znth size nd slots) size size nd.
Proof.
  intros Hsize [Horder Hmax]. unfold PianoHeapPush. split.
  - unfold FrontierPushPrefix. split; [apply Zlength_replace_Znth|].
    rewrite (piano_prefix_append _ _ _ default_node) by lia.
    apply (Permutation_app_comm [nd] (sublist 0 size slots)).
  - rewrite (piano_prefix_append _ _ _ default_node) by lia. rewrite map_app; simpl.
    apply PushLoopState_forget. apply piano_scalar_push_start; try lia.
    + rewrite piano_map_length, Zlength_sublist0 by lia; reflexivity.
    + apply (proj2 (piano_order_prefix slots size ltac:(lia))); exact Horder.
Qed.
Lemma piano_swap_values slots i j :
  map node_value (PianoSwap slots i j) =
  replace_Znth j (Znth i (map node_value slots) 0)
    (replace_Znth i (Znth j (map node_value slots) 0) (map node_value slots)).
Proof.
  unfold PianoSwap. rewrite !piano_map_replace.
  rewrite <- (piano_map_Znth node_value i slots default_node).
  rewrite <- (piano_map_Znth node_value j slots default_node). reflexivity.
Qed.
Lemma piano_push_swap before current size child nd :
  0 <= size < Zlength current -> 0 < child <= size ->
  PianoHeapPush before current size child nd ->
  node_value (Znth (heap_parent child) current default_node) <
  node_value (Znth child current default_node) ->
  PianoHeapPush before (PianoSwap current (heap_parent child) child) size (heap_parent child) nd.
Proof.
  intros Hsize Hchild [Hperm Hloop] Hlt.
  pose proof (heap_parent_positive_bounds__push_sift_up child size ltac:(lia) ltac:(lia)) as Hp.
  assert (Hread : forall i, 0 <= i < size + 1 ->
    Znth i (map node_value (sublist 0 (size + 1) current)) 0 =
    node_value (Znth i current default_node)).
  { intros i Hi. rewrite piano_map_sublist, Znth_sublist0 by lia.
    exact (piano_map_Znth node_value i current default_node). }
  unfold PianoHeapPush. split.
  - destruct Hperm as [Hlen Hperm]. split; [unfold PianoSwap; rewrite !Zlength_replace_Znth; exact Hlen|].
    rewrite piano_swap_prefix by lia.
    eapply Permutation_trans; [exact Hperm|]. apply piano_swap_permutation;
      rewrite Zlength_sublist0 by lia; lia.
  - rewrite piano_swap_prefix by lia. rewrite piano_swap_values.
    apply PushLoopState_forget.
    apply (proj2 (HeapProofFacts.push_swap_advances_loop__push_sift_up
      _ _ size child (heap_parent child) (node_value nd)
      (proj1 (PushLoopState_compat _ _ size child (node_value nd) ltac:(lia) ltac:(lia)) Hloop)
      ltac:(lia) eq_refl ltac:(rewrite !Hread by lia; exact Hlt))).
Qed.
Lemma piano_push_finish before current size child nd :
  0 <= size < Zlength current -> 0 <= child <= size ->
  PianoHeapPush before current size child nd ->
  (child = 0 \/ node_value (Znth child current default_node) <=
    node_value (Znth (heap_parent child) current default_node)) ->
  NodeHeapState current (size + 1) /\ FrontierPushPrefix before size nd current.
Proof.
  intros Hsize Hchild [Hperm Hloop] Hstop. split; [|exact Hperm].
  apply piano_heap_from_order; [lia|]. apply (proj1 (piano_order_prefix current (size + 1) ltac:(lia))).
  destruct Hloop as (_ & _ & _ & _ & Hexcept & _).
  intros i Hi. destruct (Z.eq_dec i child) as [->|Hne].
  - destruct Hstop as [->|Hle]; [lia|].
    pose proof (heap_parent_positive_bounds__push_sift_up child size ltac:(lia) ltac:(lia)) as Hp.
    rewrite !piano_map_sublist, !Znth_sublist0 by lia.
    change (Znth (heap_parent child) (map node_value current) (node_value default_node) >=
      Znth child (map node_value current) (node_value default_node)).
    rewrite !piano_map_Znth; lia.
  - apply Hexcept; lia.
Qed.

Lemma piano_pop_remaining {A} (d : A) :
  forall (before : list A) size,
    1 < size ->
    Zlength before = size ->
    Permutation
      (sublist 0 (size - 1)
        (replace_Znth 0 (Znth (size - 1) before d) before))
      (sublist 1 size before).
Proof.
  intros before size Hsize Hlength.
  destruct before as [|head tail].
  - rewrite Zlength_nil in Hlength. lia.
  - rewrite Zlength_cons in Hlength.
    change
      (Permutation
        (sublist 0 (size - 1)
          (Znth (size - 1) (head :: tail) d :: tail))
        (sublist 1 size (head :: tail))).
    rewrite Znth_cons by lia.
    rewrite sublist_cons1 by lia.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
    replace (1 - 1) with 0 by lia.
    replace (size - 1 - 1) with (size - 2) by lia.
    rewrite (sublist_split 0 (size - 1) (size - 2) tail) by lia.
    replace (size - 1) with (size - 2 + 1) by lia.
    rewrite (sublist_single d (size - 2) tail) by lia.
    change
      (Permutation
        ([Znth (size - 2) tail d] ++ sublist 0 (size - 2) tail)
        (sublist 0 (size - 2) tail ++ [Znth (size - 2) tail d])).
    apply Permutation_app_comm.
Qed.

Lemma piano_prefix_cons (xs : list Node) n :
  0 < n <= Zlength xs -> sublist 0 n xs = Znth 0 xs default_node :: sublist 1 n xs.
Proof.
  intros Hn. rewrite (sublist_split 0 n 1) by lia.
  pose proof (sublist_single default_node 0 xs ltac:(lia)) as Hsingle.
  replace (0 + 1) with 1 in Hsingle by lia. rewrite Hsingle; reflexivity.
Qed.
Lemma piano_pop_start slots size :
  1 < size <= Zlength slots -> NodeHeapState slots size ->
  PianoHeapPop slots (replace_Znth 0 (Znth (size - 1) slots default_node) slots) size 0.
Proof.
  intros Hsize [Horder Hmax]. unfold PianoHeapPop; split.
  - unfold FrontierPopTop, FrontierPopPrefix. split; [apply Zlength_replace_Znth|].
    split.
    + unfold heap_top_node. rewrite piano_prefix_cons by lia; left; reflexivity.
    + assert (Hremain : Permutation
        (sublist 0 (size - 1) (replace_Znth 0 (Znth (size - 1) slots default_node) slots))
        (sublist 1 size slots)).
      { pose proof (piano_pop_remaining default_node (sublist 0 size slots) size
          ltac:(lia) ltac:(rewrite Zlength_sublist0 by lia; reflexivity)) as H.
        rewrite Znth_sublist0 in H by lia.
        rewrite <- (piano_prefix_set _ _ _ _ default_node) in H by lia.
        rewrite !Zsublist_Zsublist0 in H by lia. exact H. }
      rewrite (piano_prefix_cons slots size ltac:(lia)). unfold heap_top_node. apply perm_skip; exact Hremain.
  - rewrite (piano_prefix_set _ _ _ _ default_node) by lia.
    rewrite piano_map_replace.
    replace (node_value (Znth (size - 1) slots default_node))
      with (Znth (size - 1) (map node_value (sublist 0 size slots)) 0).
    2:{ rewrite piano_map_sublist, Znth_sublist0 by lia.
        exact (piano_map_Znth node_value (size - 1) slots default_node). }
    apply PopLoopState_forget. apply HeapProofFacts.pop_root_replacement_loop_state__pop_initialization.
    + lia.
    + rewrite piano_map_length, Zlength_sublist0 by lia; reflexivity.
    + apply (proj2 (piano_order_prefix slots size ltac:(lia))); assumption.
Qed.
Lemma piano_pop_swap before current size index selected :
  1 < size <= Zlength current -> 0 <= index < size - 1 -> 0 <= selected < size - 1 ->
  PianoHeapPop before current size index -> PianoHeapSelected current (size - 1) index selected ->
  node_value (Znth index current default_node) < node_value (Znth selected current default_node) ->
  PianoHeapPop before (PianoSwap current index selected) size selected.
Proof.
  intros Hsize Hi Hs [Hperm Hloop] Hselected Hlt.
  unfold PianoHeapSelected in Hselected. replace (size - 1 + 1) with size in Hselected by lia.
  pose proof (PopSelectedChild_forward _ (size - 1) index selected ltac:(lia) Hselected) as Hforward.
  unfold PianoHeapPop; split.
  - destruct Hperm as [Hlen [Hin Hperm]]. split; [unfold PianoSwap; rewrite !Zlength_replace_Znth; exact Hlen|].
    split; [exact Hin|]. rewrite piano_swap_prefix by lia.
    eapply Permutation_trans; [|exact Hperm]. apply perm_skip. apply Permutation_sym.
    apply piano_swap_permutation; rewrite Zlength_sublist0 by lia; lia.
  - rewrite piano_swap_prefix by lia. rewrite piano_swap_values.
    apply PopLoopState_forget. eapply HeapProofFacts.pop_swap_advances_loop__pop_swap_transition.
    + apply (proj1 (PopLoopState_compat _ _ size index ltac:(lia) Hi)); exact Hloop.
    + apply (proj1 (PopSelectedChild_compat _ (size - 1) index selected Hi Hforward Hs)); exact Hselected.
    + rewrite !piano_map_sublist, !Znth_sublist0 by lia.
      change (Znth index (map node_value current) (node_value default_node) <
        Znth selected (map node_value current) (node_value default_node)).
      rewrite !piano_map_Znth; exact Hlt.
Qed.
Lemma piano_pop_finish before current size index :
  1 < size <= Zlength current -> 0 <= index < size - 1 ->
  PianoHeapPop before current size index ->
  (index * 2 + 1 >= size - 1 \/ exists selected,
    0 <= selected < size - 1 /\ PianoHeapSelected current (size - 1) index selected /\
    node_value (Znth selected current default_node) <= node_value (Znth index current default_node)) ->
  NodeHeapState current (size - 1) /\ FrontierPopTop before size current.
Proof.
  intros Hsize Hi [Hperm Hloop] Hstop. split; [|exact Hperm].
  apply piano_heap_from_order; [lia|].
  assert (Hordered : heap_ordered (map node_value (sublist 0 size current)) (size - 1)).
  { pose proof (proj1 (PopLoopState_compat _ _ size index ltac:(lia) Hi) Hloop) as Hlegacy.
    pose proof Hlegacy as (_ & Hb & Hc & _ & _ & Hord & _).
    assert (Hmax : HeapProofFacts.PrefixMaximum (map node_value (sublist 0 size before)) size
      (Znth 0 (map node_value (sublist 0 size before)) 0)).
    { unfold HeapProofFacts.PrefixMaximum. repeat split; try lia.
      intros j Hj. apply heap_ordered_root_upper_bound__pop_initialization with (size := size); auto. }
    assert (Hready : HeapProofFacts.PopReadyState
      (map node_value (sublist 0 size before)) (map node_value (sublist 0 size current)) size
      (Znth 0 (map node_value (sublist 0 size before)) 0)).
    { destruct Hstop as [Hleaf|[selected [Hs [Hsel Hle]]]].
      - eapply HeapProofFacts.pop_leaf_ready__pop_ready_exit; eauto.
      - unfold PianoHeapSelected in Hsel. replace (size - 1 + 1) with size in Hsel by lia.
        pose proof (PopSelectedChild_forward _ (size - 1) index selected ltac:(lia) Hsel) as Hforward.
        eapply HeapProofFacts.pop_comparison_ready__pop_ready_exit; [exact Hmax|exact Hlegacy| |].
        + apply (proj1 (PopSelectedChild_compat _ (size - 1) index selected Hi Hforward Hs)); exact Hsel.
        + rewrite !piano_map_sublist, !Znth_sublist0 by lia.
          change (Znth index (map node_value current) (node_value default_node) >=
            Znth selected (map node_value current) (node_value default_node)).
          rewrite !piano_map_Znth; lia. }
    destruct Hready as (_ & _ & _ & _ & _ & _ & _ & Hord'). exact Hord'. }
  unfold heap_ordered in *. intros child Hchild.
  specialize (Hordered child Hchild).
  pose proof (heap_parent_positive_bounds__push_sift_up child size ltac:(lia) ltac:(lia)) as Hp.
  rewrite piano_map_sublist, !Znth_sublist0 in Hordered by lia. exact Hordered.
Qed.

Lemma piano_nodes_wf vals starts los his bests :
  Zlength starts = Zlength vals -> Zlength los = Zlength vals ->
  Zlength his = Zlength vals -> Zlength bests = Zlength vals ->
  NodeArrays (PianoNodes vals starts los his bests) vals starts los his bests.
Proof.
  revert starts los his bests. induction vals as [|v vals IH]; intros starts los his bests Hs Hl Hh Hb;
  destruct starts as [|s starts]; destruct los as [|l los]; destruct his as [|h his];
  destruct bests as [|b bests]; rewrite ?Zlength_cons, ?Zlength_nil in *;
    try (pose proof (Zlength_nonneg vals); lia);
    try (pose proof (Zlength_nonneg starts); lia);
    try (pose proof (Zlength_nonneg los); lia);
    try (pose proof (Zlength_nonneg his); lia);
    try (pose proof (Zlength_nonneg bests); lia).
  - unfold NodeArrays, PianoNodes; simpl. repeat split; constructor.
  - specialize (IH starts los his bests ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct IH as (Hv & Hs' & Hl' & Hh' & Hb').
    unfold NodeArrays. cbn [PianoNodes]. repeat split; constructor; auto.
Qed.
Lemma piano_arrays_length slots vals starts los his bests :
  NodeArrays slots vals starts los his bests -> Zlength vals = Zlength slots.
Proof. rewrite piano_arrays_iff. intros (-> & _). apply piano_map_length. Qed.
Lemma piano_initial_node ps n L R start lo hi best value :
  Zlength ps = n + 1 -> 1 <= L <= R -> R <= n ->
  1 <= start <= n - L + 1 -> lo = start + L - 1 -> hi = Z.min n (start + R - 1) ->
  RangeArgmax ps lo hi best -> value = Znth best ps 0 - Znth (start - 1) ps 0 ->
  ValidNodeFields ps n L R value start lo hi best.
Proof.
  intros Hps HLR HR Hstart Hlo Hhi Harg Hvalue.
  apply piano_argmax_view in Harg. destruct Harg as [Hb Hmax].
  unfold ValidNodeFields. apply ValidNode_unfold. cbn.
  repeat split; try lia. intros finish Hfinish. specialize (Hmax finish Hfinish); lia.
Qed.
Lemma piano_initial_empty ps n L R : PianoInitialPrefix ps n L R 1 [].
Proof. split; [constructor|]. change (@Permutation Z [] []). reflexivity. Qed.
Lemma piano_Zrange_snoc lo hi : lo <= hi -> Zrange lo (hi + 1) = Zrange lo hi ++ [hi].
Proof.
  intros H. unfold Zrange.
  replace (Z.to_nat (hi + 1 - lo)) with (Z.to_nat (hi - lo) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  rewrite Z2Nat.id by lia. replace (lo + (hi - lo)) with hi by lia. reflexivity.
Qed.
Lemma piano_initial_step ps n L R start nodes out nd :
  1 <= start -> PianoInitialPrefix ps n L R start nodes ->
  ValidNode ps n L R nd -> node_start nd = start -> node_lo nd = start + L - 1 ->
  node_hi nd = Z.min n (start + R - 1) ->
  Permutation (nd :: nodes) out -> PianoInitialPrefix ps n L R (start + 1) out.
Proof.
  intros Hstart [Hnodes Hstarts] Hnd Hs Hl Hh Hperm. split.
  - eapply Forall_permutation; [exact Hperm|]. constructor.
    + split; [exact Hnd|]. rewrite Hs. repeat split; try assumption; lia.
    + eapply Forall_impl; [|exact Hnodes]. intros x (Hv & Hr & Hlo & Hhi).
      split; [exact Hv|]. repeat split; try assumption; lia.
  - rewrite piano_Zrange_snoc by lia.
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_map; exact Hperm|].
    simpl. rewrite Hs. eapply Permutation_trans.
    + apply perm_skip; exact Hstarts.
    + apply (Permutation_app_comm [start] (Zrange 1 start)).
Qed.
Lemma piano_nodup_map_injective {A B} (f : A -> B) xs x y :
  NoDup (map f xs) -> In x xs -> In y xs -> f x = f y -> x = y.
Proof.
  induction xs as [|a xs IH]; simpl; intros Hnodup Hx Hy Heq; [contradiction|].
  inversion Hnodup as [|? ? Hnot Htail]; subst. destruct Hx as [->|Hx], Hy as [->|Hy]; auto.
  - exfalso. apply Hnot. rewrite Heq. apply in_map; exact Hy.
  - exfalso. apply Hnot. rewrite <- Heq. apply in_map; exact Hx.
Qed.
Lemma piano_initial_complete ps n L R nodes :
  1 <= L <= R -> R <= n -> PianoInitialPrefix ps n L R (n - L + 2) nodes ->
  InitialFrontierState ps n L R nodes.
Proof.
  intros HLR HR [Hnodes Hstarts].
  assert (Hunique : NoDup (map node_start nodes)).
  { eapply Permutation_NoDup; [apply Permutation_sym; exact Hstarts|]. apply NoDup_Zrange. }
  unfold InitialFrontierState, FrontierState.
  split; [unfold ValidSongCodes; repeat split; constructor|].
  split; [unfold SongCodesSum; reflexivity|].
  split; [intros picked rest Hin; contradiction|].
  split.
  - eapply Forall_impl; [|exact Hnodes]. intros nd H. exact (proj1 H).
  - split.
    + split.
      * eapply NoDup_map_inv; exact Hunique.
      * intros nd1 nd2 H1 H2 Hne Heq. exfalso. apply Hne.
        eapply piano_nodup_map_injective; eauto.
    + split.
      * intros code Hvalid Hnot. unfold ValidChordCode in Hvalid.
        destruct Hvalid as (Hps & Hlo & Horder & Hhi & Hlenlo & Hlenhi).
        assert (Hin : In (CodeStart n code) (map node_start nodes)).
        { eapply Permutation_in; [apply Permutation_sym; exact Hstarts|]. apply In_Zrange; lia. }
        apply in_map_iff in Hin. destruct Hin as [nd [Heq Hin]]. exists nd; split; [exact Hin|].
        rewrite Forall_forall in Hnodes. specialize (Hnodes nd Hin).
        destruct Hnodes as (_ & _ & Hndlo & Hndhi).
        unfold NodeCoversCode. rewrite Heq, Hndlo, Hndhi, Heq.
        split; [reflexivity|]. split; [lia|]. apply Z.min_glb; lia.
      * intros nd code Hin Hcover Hchosen; contradiction.
Qed.

Lemma piano_selected_left slots size index :
  0 <= index -> index * 2 + 1 < size -> size + 1 <= Zlength slots ->
  (index * 2 + 2 >= size \/
   node_value (Znth (index * 2 + 1) slots default_node) >=
   node_value (Znth (index * 2 + 2) slots default_node)) ->
  PianoHeapSelected slots size index (index * 2 + 1).
Proof.
  intros Hi Hl Hlen Hchoice. unfold PianoHeapSelected.
  apply PopSelectedChild_forget. apply HeapProofFacts.pop_select_left__pop_child_selection;
    unfold heap_left_child, heap_right_child; try lia.
  destruct Hchoice as [Hout|Hle]; [left; auto|]. right.
  rewrite !piano_map_sublist, !Znth_sublist0 by lia.
  change (Znth (index * 2 + 1) (map node_value slots) (node_value default_node) >=
    Znth (index * 2 + 2) (map node_value slots) (node_value default_node)).
  rewrite !piano_map_Znth; exact Hle.
Qed.
Lemma piano_selected_right slots size index :
  0 <= index -> index * 2 + 2 < size -> size + 1 <= Zlength slots ->
  node_value (Znth (index * 2 + 1) slots default_node) <
    node_value (Znth (index * 2 + 2) slots default_node) ->
  PianoHeapSelected slots size index (index * 2 + 2).
Proof.
  intros Hi Hr Hlen Hlt. unfold PianoHeapSelected.
  apply PopSelectedChild_forget. apply HeapProofFacts.pop_select_right__pop_child_selection;
    unfold heap_left_child, heap_right_child; try lia.
  rewrite !piano_map_sublist, !Znth_sublist0 by lia.
  change (Znth (index * 2 + 1) (map node_value slots) (node_value default_node) <
    Znth (index * 2 + 2) (map node_value slots) (node_value default_node)).
  rewrite !piano_map_Znth; exact Hlt.
Qed.
Lemma piano_pop_singleton slots :
  1 <= Zlength slots -> NodeHeapState slots 0 /\ FrontierPopTop slots 1 slots.
Proof.
  intros Hlen. split.
  - apply piano_heap_from_order; [lia|]. intros child H; lia.
  - unfold FrontierPopTop, FrontierPopPrefix. split; [reflexivity|]. split.
    + unfold heap_top_node. rewrite piano_prefix_cons by lia. left; reflexivity.
    + rewrite (piano_prefix_cons slots 1 ltac:(lia)).
      replace (1 - 1) with 0 by lia. rewrite !Zsublist_nil by lia.
      unfold heap_top_node; reflexivity.
Qed.

Lemma piano_arrays_node slots vals starts los his bests i :
  NodeArrays slots vals starts los his bests ->
  mkNode (Znth i vals 0) (Znth i starts 0) (Znth i los 0) (Znth i his 0) (Znth i bests 0) =
    Znth i slots default_node.
Proof.
  intros H. pose proof (piano_arrays_read slots vals starts los his bests i H)
    as (Hv & Hs & Hl & Hh & Hb).
  rewrite Hv, Hs, Hl, Hh, Hb.
  destruct (Znth i slots default_node) as [[[[v s] l] h] b]; reflexivity.
Qed.
Lemma piano_prefix_bounds l ps n :
  PrefixSums l ps -> Zlength l = n -> 0 <= n <= 100000 ->
  Forall (Z.le (-1000)) l -> Forall (Z.ge 1000) l ->
  Forall (Z.le (-100000000)) ps /\ Forall (Z.ge 100000000) ps.
Proof.
  intros Hps Hlen Hn Hlo Hhi. pose proof (proj1 Hps) as Hpslen.
  apply PrefixSums_recurrence in Hps. rewrite Hlen in Hps, Hpslen.
  assert (Hl : forall i, 0 <= i < n -> -1000 <= Znth i l 0 <= 1000).
  { intros i Hi. pose proof (proj1 (Forall_Znth _ 0 l) Hlo i ltac:(lia)).
    pose proof (proj1 (Forall_Znth _ 0 l) Hhi i ltac:(lia)). lia. }
  split; apply (proj2 (Forall_Znth _ 0 ps)); intros i Hi;
    pose proof (PrefixArrayPrefix_entry_abs_bound l ps n i Hps Hl ltac:(lia)); lia.
Qed.
