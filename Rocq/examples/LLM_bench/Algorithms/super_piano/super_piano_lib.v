Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ST_LEVELS : Z := 17.

Definition PrefixArrayPrefix
    (l pref : list Z) (upto : Z) : Prop :=
  0 <= upto /\
  upto <= Zlength l /\
  Zlength pref = upto + 1 /\
  Znth 0 pref 0 = 0 /\
  forall i,
    0 <= i < upto ->
    Znth (i + 1) pref 0 = Znth i pref 0 + Znth i l 0.

Definition PrefixSums (l pref : list Z) : Prop :=
  PrefixArrayPrefix l pref (Zlength l).

Definition SparseArgmaxBuilt
    (ps st_slots : list Z) (len : Z) : Prop :=
  Zlength ps = len /\
  Zlength st_slots = len * ST_LEVELS.

Definition RangeArgmax
    (ps : list Z) (lo hi best : Z) : Prop :=
  0 <= lo /\
  lo <= best /\
  best <= hi /\
  hi < Zlength ps /\
  forall idx,
    lo <= idx <= hi ->
    Znth idx ps 0 <= Znth best ps 0.

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
  Zlength vals = Zlength slots /\
  Zlength starts = Zlength slots /\
  Zlength los = Zlength slots /\
  Zlength his = Zlength slots /\
  Zlength bests = Zlength slots /\
  forall idx,
    0 <= idx < Zlength slots ->
    Znth idx vals 0 = node_value (Znth idx slots default_node) /\
    Znth idx starts 0 = node_start (Znth idx slots default_node) /\
    Znth idx los 0 = node_lo (Znth idx slots default_node) /\
    Znth idx his 0 = node_hi (Znth idx slots default_node) /\
    Znth idx bests 0 = node_best (Znth idx slots default_node).

Definition NodeHeapState (slots : list Node) (size : Z) : Prop :=
  0 <= size /\
  size <= Zlength slots /\
  (0 < size ->
    forall idx,
      0 <= idx < size ->
      node_value (Znth idx slots default_node) <=
      node_value (Znth 0 slots default_node)).

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
  forall finish,
    node_lo nd <= finish <= node_hi nd ->
    Znth finish ps 0 - Znth (node_start nd - 1) ps 0 <= node_value nd.

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
  intros l pref upto i [Hupto0 [Huptolen [Hpreflen [Hpref0 Hstep]]]] Hbound Hi.
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
    [Hupto0 [Huptolen [Hlen1 [Hzero1 Hstep1]]]]
    [_ [_ [Hlen2 [Hzero2 Hstep2]]]].
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
  unfold PrefixSums in *.
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
  unfold PrefixSums in Hpref.
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
  unfold ValidNodeFields, ValidNode in Hvalid.
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
  unfold ValidNodeFields, ValidNode, ValidChordCode in *.
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
  unfold ValidNodeFields, ValidNode, NodeCoversCode in *.
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
  unfold ValidNodeFields, ValidNode in Hvalid.
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
  unfold ValidNode, NodeCoversCode in *.
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
    0 < size ->
    NodeHeapState slots size ->
    In nd (sublist 0 size slots) ->
    node_value nd <= heap_top_value slots.
Proof.
  intros slots size nd Hsize_pos Hheap Hin.
  destruct Hheap as [Hsize_nonneg [Hsize_le Hbound]].
  destruct (in_sublist0_Znth default_node size slots nd (conj Hsize_nonneg Hsize_le) Hin)
    as [i [Hi Hz]].
  rewrite <- Hz.
  unfold heap_top_value, heap_top_node.
  apply Hbound.
  - exact Hsize_pos.
  - exact Hi.
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
  unfold ValidNodeFields, ValidNode, RangeArgmax in *.
  cbn in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi [_ Hmax_old]]]]]]]]].
  destruct Harg as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
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
  unfold ValidNodeFields, ValidNode, RangeArgmax in *.
  cbn in *.
  destruct Hvalid as
      [Hlen [Hstart1 [Hstartn [HloL [Hlohi [Hhin [Hlobest [Hbesthi [_ _]]]]]]]]].
  destruct Harg as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
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
    unfold ValidNodeFields, ValidNode in Hvalid.
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
        destruct Hleft as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
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
        destruct Hright as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
            unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
          unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
    unfold ValidNodeFields, ValidNode in Hvalid.
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
          unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
      destruct Hleft as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
      assert (Hbest_le_hi : best <= hi).
      {
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
        unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
            unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
          unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
    unfold ValidNodeFields, ValidNode in Hvalid.
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
    unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
      destruct Hright as [Hlo_ret [Hret_hi [Hret_best [Hhi_n Hmax]]]].
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
          unfold ValidNodeFields, ValidNode in Hvalid; cbn in Hvalid.
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
    unfold ValidNodeFields, ValidNode in Hvalid.
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
