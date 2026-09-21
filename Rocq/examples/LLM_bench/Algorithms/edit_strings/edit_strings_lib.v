Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition edit_zrange (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition edit_zrange_between (lo hi : Z) : list Z :=
  map (fun off => lo + Z.of_nat off) (seq 0 (Z.to_nat (hi - lo))).

Definition EditBinaryList (xs : list Z) (n : Z) : Prop :=
  Zlength xs = n /\
  forall idx, 0 <= idx < n -> Znth idx xs 0 = 0 \/ Znth idx xs 0 = 1.

Definition edit_edge_open (t : list Z) (idx : Z) : Prop :=
  Znth (idx - 1) t 0 = 1 /\ Znth idx t 0 = 1.

Definition edit_edge_openb (t : list Z) (idx : Z) : bool :=
  Z.eqb (Znth (idx - 1) t 0) 1 && Z.eqb (Znth idx t 0) 1.

Definition edit_all_edges_openb (t : list Z) (lo hi : Z) : bool :=
  forallb (edit_edge_openb t) (edit_zrange_between lo hi).

Definition EditBlockStart (t : list Z) (idx start : Z) : Prop :=
  0 <= start <= idx /\
  (forall k, start < k <= idx -> edit_edge_open t k) /\
  (start = 0 \/ ~ edit_edge_open t start).

Definition edit_block_startb (t : list Z) (idx start : Z) : bool :=
  Z.leb 0 start &&
  Z.leb start idx &&
  edit_all_edges_openb t (start + 1) (idx + 1) &&
  (Z.eqb start 0 || negb (edit_edge_openb t start)).

Definition edit_bit_atb (xs : list Z) (idx bit : Z) : bool :=
  Z.eqb (Znth idx xs 0) bit.

Definition edit_count_bit_in_block_prefix
    (s t : list Z) (limit block bit : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun idx =>
             Z.ltb idx limit &&
             edit_block_startb t idx block &&
             edit_bit_atb s idx bit)
          (edit_zrange (Zlength s)))).

Definition EditZeroPrefix (xs : list Z) (written : Z) : Prop :=
  Zlength xs = written /\
  forall idx, 0 <= idx < written -> Znth idx xs 0 = 0.

Definition EditZeroFull (n : Z) (xs : list Z) : Prop :=
  Zlength xs = n /\
  forall idx, 0 <= idx < n -> Znth idx xs 0 = 0.

Definition EditSegmentPrefix (t : list Z) (upto : Z) (seg : list Z) : Prop :=
  Zlength seg = upto /\
  forall idx, 0 <= idx < upto -> EditBlockStart t idx (Znth idx seg 0).

Definition EditCountsForPrefix
    (s t : list Z) (n upto : Z) (cnt0 cnt1 : list Z) : Prop :=
  Zlength cnt0 = n /\
  Zlength cnt1 = n /\
  (forall block,
      0 <= block < n ->
      Znth block cnt0 0 = edit_count_bit_in_block_prefix s t upto block 0) /\
  (forall block,
      0 <= block < n ->
      Znth block cnt1 0 = edit_count_bit_in_block_prefix s t upto block 1).

Definition EditBuildState
    (s t : list Z) (n upto : Z)
    (seg cnt0 cnt1 : list Z) : Prop :=
  0 <= upto <= n /\
  EditBinaryList s n /\
  EditBinaryList t n /\
  EditSegmentPrefix t upto seg /\
  EditCountsForPrefix s t n upto cnt0 cnt1.

Definition EditCountBounds (n : Z) (cnt : list Z) : Prop :=
  Zlength cnt = n /\
  forall idx, 0 <= idx < n -> 0 <= Znth idx cnt 0 <= n.

Definition EditScratchCountsBound
    (n : Z) (cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  EditCountBounds n cnt10 /\
  EditCountBounds n cnt11 /\
  EditCountBounds n cnt20 /\
  EditCountBounds n cnt21.

Definition edit_count_positions_in_seg_prefix
    (seg : list Z) (limit block : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun idx =>
             Z.ltb idx limit &&
             Z.eqb (Znth idx seg 0) block)
          (edit_zrange (Zlength seg)))).

Definition EditGreedyRemainingTotals
    (seg1 seg2 : list Z) (i : Z)
    (full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  (forall block,
      0 <= block < Zlength seg1 ->
      Znth block cnt10 0 + Znth block cnt11 0 =
      Znth block full10 0 + Znth block full11 0 -
      edit_count_positions_in_seg_prefix seg1 i block) /\
  (forall block,
      0 <= block < Zlength seg2 ->
      Znth block cnt20 0 + Znth block cnt21 0 =
      Znth block full20 0 + Znth block full21 0 -
      edit_count_positions_in_seg_prefix seg2 i block).

Definition EditReachableString (s t out : list Z) (n : Z) : Prop :=
  EditBinaryList s n /\
  EditBinaryList t n /\
  EditBinaryList out n /\
  forall block bit,
    0 <= block < n ->
    (bit = 0 \/ bit = 1) ->
    edit_count_bit_in_block_prefix out t n block bit =
    edit_count_bit_in_block_prefix s t n block bit.

Definition edit_match_count (s1 s2 : list Z) (n : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun idx => Z.eqb (Znth idx s1 0) (Znth idx s2 0))
          (edit_zrange n))).

Definition EditStringsFeasibleMatchCount
    (s1 s2 t1 t2 : list Z) (n answer : Z) : Prop :=
  exists out1 out2,
    EditReachableString s1 t1 out1 n /\
    EditReachableString s2 t2 out2 n /\
    answer = edit_match_count out1 out2 n.

Definition EditStringsMatchUpperBound
    (s1 s2 t1 t2 : list Z) (n answer : Z) : Prop :=
  forall cand1 cand2 cand,
    EditReachableString s1 t1 cand1 n ->
    EditReachableString s2 t2 cand2 n ->
    cand = edit_match_count cand1 cand2 n ->
    cand <= answer.

Definition EditStringsMaximum
    (s1 s2 t1 t2 : list Z) (n answer : Z) : Prop :=
  EditBinaryList s1 n /\
  EditBinaryList s2 n /\
  EditBinaryList t1 n /\
  EditBinaryList t2 n /\
  EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer /\
  EditStringsMatchUpperBound s1 s2 t1 t2 n answer.

Lemma EditStringsMaximum_intro :
  forall s1 s2 t1 t2 n answer,
    EditBinaryList s1 n ->
    EditBinaryList s2 n ->
    EditBinaryList t1 n ->
    EditBinaryList t2 n ->
    EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer ->
    EditStringsMatchUpperBound s1 s2 t1 t2 n answer ->
    EditStringsMaximum s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer Hs1 Hs2 Ht1 Ht2 Hfeasible Hupper.
  unfold EditStringsMaximum.
  split; [exact Hs1|].
  split; [exact Hs2|].
  split; [exact Ht1|].
  split; [exact Ht2|].
  split; [exact Hfeasible|exact Hupper].
Qed.

Lemma EditStringsMaximum_feasible :
  forall s1 s2 t1 t2 n answer,
    EditStringsMaximum s1 s2 t1 t2 n answer ->
    EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer Hmax.
  unfold EditStringsMaximum in Hmax.
  destruct Hmax as [_ [_ [_ [_ [Hfeasible _]]]]].
  exact Hfeasible.
Qed.

Lemma EditStringsMaximum_upper_bound :
  forall s1 s2 t1 t2 n answer,
    EditStringsMaximum s1 s2 t1 t2 n answer ->
    EditStringsMatchUpperBound s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer Hmax.
  unfold EditStringsMaximum in Hmax.
  destruct Hmax as [_ [_ [_ [_ [_ Hupper]]]]].
  exact Hupper.
Qed.

Inductive EditGreedyConsumedPrefix
    (seg1 seg2 : list Z)
    (full10 full11 full20 full21 : list Z) :
    Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop :=
  | EditGreedyConsumedPrefix_start :
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
        0 0 full10 full11 full20 full21
  | EditGreedyConsumedPrefix_common_zero :
      forall i ans cnt10 cnt11 cnt20 cnt21 a b,
        0 <= i < Zlength seg1 ->
        Zlength seg2 = Zlength seg1 ->
        a = Znth i seg1 0 ->
        b = Znth i seg2 0 ->
        0 < Znth a cnt10 0 ->
        0 < Znth b cnt20 0 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          i ans cnt10 cnt11 cnt20 cnt21 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          (i + 1) (ans + 1)
          (replace_Znth a (Znth a cnt10 0 - 1) cnt10)
          cnt11
          (replace_Znth b (Znth b cnt20 0 - 1) cnt20)
          cnt21
  | EditGreedyConsumedPrefix_common_one :
      forall i ans cnt10 cnt11 cnt20 cnt21 a b,
        0 <= i < Zlength seg1 ->
        Zlength seg2 = Zlength seg1 ->
        a = Znth i seg1 0 ->
        b = Znth i seg2 0 ->
        ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
        0 < Znth a cnt11 0 ->
        0 < Znth b cnt21 0 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          i ans cnt10 cnt11 cnt20 cnt21 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          (i + 1) (ans + 1)
          cnt10
          (replace_Znth a (Znth a cnt11 0 - 1) cnt11)
          cnt20
          (replace_Znth b (Znth b cnt21 0 - 1) cnt21)
  | EditGreedyConsumedPrefix_s1_zero_s2_one :
      forall i ans cnt10 cnt11 cnt20 cnt21 a b,
        0 <= i < Zlength seg1 ->
        Zlength seg2 = Zlength seg1 ->
        a = Znth i seg1 0 ->
        b = Znth i seg2 0 ->
        ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
        ~ (0 < Znth a cnt11 0 /\ 0 < Znth b cnt21 0) ->
        0 < Znth a cnt10 0 ->
        0 < Znth b cnt21 0 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          i ans cnt10 cnt11 cnt20 cnt21 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          (i + 1) ans
          (replace_Znth a (Znth a cnt10 0 - 1) cnt10)
          cnt11
          cnt20
          (replace_Znth b (Znth b cnt21 0 - 1) cnt21)
  | EditGreedyConsumedPrefix_s1_one_s2_zero :
      forall i ans cnt10 cnt11 cnt20 cnt21 a b,
        0 <= i < Zlength seg1 ->
        Zlength seg2 = Zlength seg1 ->
        a = Znth i seg1 0 ->
        b = Znth i seg2 0 ->
        ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
        ~ (0 < Znth a cnt11 0 /\ 0 < Znth b cnt21 0) ->
        ~ (0 < Znth a cnt10 0) ->
        0 < Znth a cnt11 0 ->
        0 < Znth b cnt20 0 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          i ans cnt10 cnt11 cnt20 cnt21 ->
        EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
          (i + 1) ans
          cnt10
          (replace_Znth a (Znth a cnt11 0 - 1) cnt11)
          (replace_Znth b (Znth b cnt20 0 - 1) cnt20)
          cnt21.

Definition EditGreedyFinalOptimality
    (s1 s2 t1 t2 : list Z) (n answer : Z) : Prop :=
  EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer /\
  EditStringsMatchUpperBound s1 s2 t1 t2 n answer.

Definition EditGreedyPrefixState
    (s1 s2 t1 t2 : list Z) (n i answer : Z)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  0 <= i <= n /\
  0 <= answer <= i /\
  exists full10 full11 full20 full21,
    EditBuildState s1 t1 n n seg1 full10 full11 /\
    EditBuildState s2 t2 n n seg2 full20 full21 /\
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 /\
    EditGreedyRemainingTotals seg1 seg2 i
      full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 /\
    EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
      i answer cnt10 cnt11 cnt20 cnt21.

Definition EditGreedyCurrentAvailability
    (n i : Z)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  0 <= i < n ->
  0 <= Znth i seg1 0 < n /\
  0 <= Znth i seg2 0 < n /\
  0 < Znth (Znth i seg1 0) cnt10 0 +
      Znth (Znth i seg1 0) cnt11 0 /\
  0 < Znth (Znth i seg2 0) cnt20 0 +
      Znth (Znth i seg2 0) cnt21 0.

Definition EditGreedyCompletedMaximumFacts
    (s1 s2 t1 t2 : list Z) (n : Z) : Prop :=
  forall answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyPrefixState s1 s2 t1 t2 n n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer.

Definition EditGreedyCompletedStateFacts
    (s1 s2 t1 t2 : list Z) (n answer : Z)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  EditGreedyPrefixState s1 s2 t1 t2 n n answer
    seg1 seg2 cnt10 cnt11 cnt20 cnt21 /\
  EditGreedyFinalOptimality s1 s2 t1 t2 n answer.

Lemma EditGreedyPrefixState_final_optimality :
  forall s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n ->
    EditGreedyPrefixState s1 s2 t1 t2 n n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hfacts Hstate.
  exact (Hfacts answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate).
Qed.

Lemma EditGreedyPrefixState_completed_maximum :
  forall s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyPrefixState s1 s2 t1 t2 n n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n ->
    EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n.
Proof.
  intros s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hfacts.
  exact Hfacts.
Qed.

Lemma EditGreedyPrefixState_completed_state_facts :
  forall s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n ->
    EditGreedyPrefixState s1 s2 t1 t2 n n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21.
Proof.
  intros s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hfacts Hstate.
  unfold EditGreedyCompletedStateFacts.
  split; [exact Hstate|].
  eapply EditGreedyPrefixState_final_optimality; eauto.
Qed.

Lemma EditGreedyCompletedStateFacts_to_Maximum :
  forall s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditStringsMaximum s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hfacts.
  unfold EditGreedyCompletedStateFacts in Hfacts.
  destruct Hfacts as [Hstate Hopt].
  unfold EditGreedyFinalOptimality in Hopt.
  destruct Hopt as [Hfeasible Hupper].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  eapply EditStringsMaximum_intro; eauto.
Qed.

Lemma EditGreedyCompletedMaximumFacts_to_Maximum :
  forall s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n ->
    EditGreedyPrefixState s1 s2 t1 t2 n n answer
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditStringsMaximum s1 s2 t1 t2 n answer.
Proof.
  intros s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hfacts Hstate.
  pose proof (Hfacts answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate)
    as Hopt.
  unfold EditGreedyFinalOptimality in Hopt.
  destruct Hopt as [Hfeasible Hupper].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [_ [_ [full10 [full11 [full20 [full21 [Hbuild1 [Hbuild2 _]]]]]]]].
  destruct Hbuild1 as [_ [Hs1 [Ht1 _]]].
  destruct Hbuild2 as [_ [Hs2 [Ht2 _]]].
  eapply EditStringsMaximum_intro; eauto.
Qed.

Lemma EditZeroPrefix_snoc_zero__zeroing_and_base_build :
  forall xs i,
    EditZeroPrefix xs i ->
    EditZeroPrefix (xs ++ 0 :: nil) (i + 1).
Proof.
  intros xs i Hprefix.
  unfold EditZeroPrefix in *.
  destruct Hprefix as [Hlen Hzero].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros idx Hidx.
    destruct (Z_lt_dec idx i) as [Hlt | Hnlt].
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hzero; lia.
    + assert (idx = i) by lia.
      subst idx.
      rewrite app_Znth2 by lia.
      rewrite Hlen.
      replace (i - i) with 0 by lia.
      reflexivity.
Qed.
Lemma EditZeroPrefix_to_full_at_bound__zeroing_and_base_build :
  forall n xs i,
    i >= n ->
    i <= n ->
    EditZeroPrefix xs i ->
    EditZeroFull n xs.
Proof.
  intros n xs i Hge Hle Hprefix.
  unfold EditZeroPrefix in Hprefix.
  unfold EditZeroFull.
  destruct Hprefix as [Hlen Hzero].
  split; [rewrite Hlen; lia|].
  intros idx Hidx.
  apply Hzero; lia.
Qed.
Lemma EditZeroFull_count_bound__zeroing_and_base_build :
  forall n xs,
    0 <= n ->
    EditZeroFull n xs ->
    EditCountBounds n xs.
Proof.
  intros n xs Hn Hfull.
  unfold EditZeroFull in Hfull.
  unfold EditCountBounds.
  destruct Hfull as [Hlen Hzero].
  split; [exact Hlen|].
  intros idx Hidx.
  rewrite Hzero by lia.
  lia.
Qed.
Lemma EditZeroFull_scratch_bound__zeroing_and_base_build :
  forall n c10 c11 c20 c21,
    0 <= n ->
    EditZeroFull n c10 ->
    EditZeroFull n c11 ->
    EditZeroFull n c20 ->
    EditZeroFull n c21 ->
    EditScratchCountsBound n c10 c11 c20 c21.
Proof.
  intros n c10 c11 c20 c21 Hn H10 H11 H20 H21.
  unfold EditScratchCountsBound.
  repeat split;
    eapply EditZeroFull_count_bound__zeroing_and_base_build; eauto.
Qed.
Lemma edit_filter_ltb_one_seq_from__zeroing_and_base_build :
  forall start len pred1 pred2,
    1 <= Z.of_nat start ->
    filter (fun idx => andb (andb (Z.ltb idx 1) (pred1 idx)) (pred2 idx))
      (map Z.of_nat (seq start len)) = nil.
Proof.
  intros start len pred1 pred2 Hstart.
  revert start Hstart.
  induction len as [|len IH]; intros start Hstart; simpl; auto.
  replace (Z.ltb (Z.of_nat start) 1) with false
    by (symmetry; apply Z.ltb_ge; lia).
  simpl.
  apply IH.
  lia.
Qed.
Lemma edit_count_bit_in_block_prefix_one__zeroing_and_base_build :
  forall s t n block bit,
    1 <= n ->
    Zlength s = n ->
    0 <= block < n ->
    edit_count_bit_in_block_prefix s t 1 block bit =
      if Z.eq_dec block 0
      then if Z.eq_dec (Znth 0 s 0) bit then 1 else 0
      else 0.
Proof.
  intros s t n block bit Hn Hslen Hblock.
  unfold edit_count_bit_in_block_prefix, edit_zrange.
  rewrite Hslen.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
  simpl.
  rewrite (edit_filter_ltb_one_seq_from__zeroing_and_base_build
             1 (Z.to_nat (n - 1))
             (fun idx => edit_block_startb t idx block)
             (fun idx => edit_bit_atb s idx bit))
    by lia.
  simpl.
  unfold edit_block_startb, edit_all_edges_openb, edit_bit_atb, edit_zrange_between.
  destruct (Z.eq_dec block 0) as [Hblock0 | Hblock0].
  - subst block.
    replace (Z.leb 0 0) with true by reflexivity.
    replace (Z.to_nat (1 - (0 + 1))) with O by lia.
    simpl.
    replace (Z.eqb 0 0) with true by reflexivity.
    simpl.
    destruct (Z.eq_dec (Znth 0 s 0) bit) as [Heq | Hneq].
    + subst bit.
      replace (Z.eqb (Znth 0 s 0) (Znth 0 s 0)) with true
        by (symmetry; apply Z.eqb_eq; reflexivity).
      reflexivity.
    + replace (Z.eqb (Znth 0 s 0) bit) with false
        by (symmetry; apply Z.eqb_neq; exact Hneq).
      reflexivity.
  - replace (Z.leb 0 block) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.leb block 0) with false by (symmetry; apply Z.leb_gt; lia).
    simpl.
    reflexivity.
Qed.
Lemma EditCountBounds_replace_zero_inc__zeroing_and_base_build :
  forall n xs,
    1 <= n ->
    EditZeroFull n xs ->
    EditCountBounds n (replace_Znth 0 (Znth 0 xs 0 + 1) xs).
Proof.
  intros n xs Hn Hzero.
  unfold EditZeroFull in Hzero.
  destruct Hzero as [Hlen Hzero].
  unfold EditCountBounds.
  split.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros idx Hidx.
    destruct (Z.eq_dec idx 0) as [Hidx0 | Hidx0].
    + subst idx.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      rewrite Hzero by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff.
      2: { rewrite Hlen; lia. }
      2: { rewrite Hlen; lia. }
      2: { lia. }
      rewrite Hzero by lia.
      lia.
Qed.
Lemma EditScratchCountsBound_replace_c11_zero_inc__zeroing_and_base_build :
  forall n c10 c11 c20 c21,
    1 <= n ->
    EditScratchCountsBound n c10 c11 c20 c21 ->
    EditZeroFull n c11 ->
    EditScratchCountsBound n c10 (replace_Znth 0 (Znth 0 c11 0 + 1) c11) c20 c21.
Proof.
  intros n c10 c11 c20 c21 Hn Hscratch Hzero.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  split; [exact H10|].
  split.
  - eapply EditCountBounds_replace_zero_inc__zeroing_and_base_build; eauto.
  - split; [exact H20|exact H21].
Qed.
Lemma EditScratchCountsBound_replace_c10_zero_inc__zeroing_and_base_build :
  forall n c10 c11 c20 c21,
    1 <= n ->
    EditScratchCountsBound n c10 c11 c20 c21 ->
    EditZeroFull n c10 ->
    EditScratchCountsBound n (replace_Znth 0 (Znth 0 c10 0 + 1) c10) c11 c20 c21.
Proof.
  intros n c10 c11 c20 c21 Hn Hscratch Hzero.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  split.
  - eapply EditCountBounds_replace_zero_inc__zeroing_and_base_build; eauto.
  - split; [exact H11|].
    split; [exact H20|exact H21].
Qed.
Lemma EditBinaryList_from_bounds__zeroing_and_base_build :
  forall xs n,
    Zlength xs = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx xs 0 <= 1) ->
    EditBinaryList xs n.
Proof.
  intros xs n Hlen Hbounds.
  unfold EditBinaryList.
  split; [exact Hlen|].
  intros idx Hidx.
  specialize (Hbounds idx Hidx).
  lia.
Qed.
Lemma EditSegmentPrefix_one_zero__zeroing_and_base_build :
  forall t sg,
    Zlength sg = 1 ->
    Znth 0 sg 0 = 0 ->
    EditSegmentPrefix t 1 sg.
Proof.
  intros t sg Hlen Hzero.
  unfold EditSegmentPrefix.
  split; [exact Hlen|].
  intros idx Hidx.
  assert (idx = 0) by lia.
  subst idx.
  rewrite Hzero.
  unfold EditBlockStart.
  split; [lia|].
  split.
  - intros k Hk; lia.
  - left; reflexivity.
Qed.
Lemma EditCountsForPrefix_initial_one__zeroing_and_base_build :
  forall s t n cnt0 cnt1,
    1 <= n ->
    Zlength s = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    Znth 0 s 0 <> 0 ->
    EditZeroFull n cnt0 ->
    EditZeroFull n cnt1 ->
    EditCountsForPrefix s t n 1 cnt0
      (replace_Znth 0 (Znth 0 cnt1 0 + 1) cnt1).
Proof.
  intros s t n cnt0 cnt1 Hn Hslen Hsbounds Hs0nz Hcnt0 Hcnt1.
  assert (Hs0one : Znth 0 s 0 = 1).
  { specialize (Hsbounds 0 ltac:(lia)); lia. }
  unfold EditZeroFull in Hcnt0, Hcnt1.
  destruct Hcnt0 as [Hcnt0len Hcnt0zero].
  destruct Hcnt1 as [Hcnt1len Hcnt1zero].
  unfold EditCountsForPrefix.
  split; [exact Hcnt0len|].
  split; [rewrite Zlength_replace_Znth; exact Hcnt1len|].
  split.
  - intros block Hblock.
    rewrite Hcnt0zero by lia.
    rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block 0)
      by (try exact Hn; try exact Hslen; lia).
    destruct (Z.eq_dec block 0) as [Hblock0 | Hblock0].
    + subst block.
      destruct (Z.eq_dec (Znth 0 s 0) 0) as [Hz | Hz]; [lia|reflexivity].
    + reflexivity.
  - intros block Hblock.
    destruct (Z.eq_dec block 0) as [Hblock0 | Hblock0].
    + subst block.
      rewrite Znth_replace_Znth_Same by (rewrite Hcnt1len; lia).
      rewrite Hcnt1zero by lia.
      rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n 0 1)
        by (try exact Hn; try exact Hslen; lia).
      destruct (Z.eq_dec 0 0) as [_ | Hneq]; [|lia].
      rewrite Hs0one.
      destruct (Z.eq_dec 1 1) as [_ | Hneq]; [lia|lia].
    + rewrite Znth_replace_Znth_Diff.
      2: { rewrite Hcnt1len; lia. }
      2: { rewrite Hcnt1len; lia. }
      2: { lia. }
      rewrite Hcnt1zero by lia.
      rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block 1)
        by (try exact Hn; try exact Hslen; lia).
      destruct (Z.eq_dec block 0) as [Heq | _]; [lia|reflexivity].
Qed.
Lemma EditCountsForPrefix_initial_zero__zeroing_and_base_build :
  forall s t n cnt0 cnt1,
    1 <= n ->
    Zlength s = n ->
    Znth 0 s 0 = 0 ->
    EditZeroFull n cnt0 ->
    EditZeroFull n cnt1 ->
    EditCountsForPrefix s t n 1
      (replace_Znth 0 (Znth 0 cnt0 0 + 1) cnt0) cnt1.
Proof.
  intros s t n cnt0 cnt1 Hn Hslen Hs0zero Hcnt0 Hcnt1.
  unfold EditZeroFull in Hcnt0, Hcnt1.
  destruct Hcnt0 as [Hcnt0len Hcnt0zero].
  destruct Hcnt1 as [Hcnt1len Hcnt1zero].
  unfold EditCountsForPrefix.
  split; [rewrite Zlength_replace_Znth; exact Hcnt0len|].
  split; [exact Hcnt1len|].
  split.
  - intros block Hblock.
    destruct (Z.eq_dec block 0) as [Hblock0 | Hblock0].
    + subst block.
      rewrite Znth_replace_Znth_Same by (rewrite Hcnt0len; lia).
      rewrite Hcnt0zero by lia.
      rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n 0 0)
        by (try exact Hn; try exact Hslen; lia).
      destruct (Z.eq_dec 0 0) as [_ | Hneq]; [|lia].
      rewrite Hs0zero.
      destruct (Z.eq_dec 0 0) as [_ | Hneq]; [lia|lia].
    + rewrite Znth_replace_Znth_Diff.
      2: { rewrite Hcnt0len; lia. }
      2: { rewrite Hcnt0len; lia. }
      2: { lia. }
      rewrite Hcnt0zero by lia.
      rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block 0)
        by (try exact Hn; try exact Hslen; lia).
      destruct (Z.eq_dec block 0) as [Heq | _]; [lia|reflexivity].
  - intros block Hblock.
    rewrite Hcnt1zero by lia.
    rewrite (edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block 1)
      by (try exact Hn; try exact Hslen; lia).
    destruct (Z.eq_dec block 0) as [Hblock0 | Hblock0].
    + subst block.
      destruct (Z.eq_dec (Znth 0 s 0) 1) as [Hz | Hz]; [lia|reflexivity].
    + reflexivity.
Qed.
Lemma EditBuildState_initial_s1_one__zeroing_and_base_build :
  forall s t n sg cnt0 cnt1,
    1 <= n ->
    Zlength s = n ->
    Zlength t = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx t 0 <= 1) ->
    Znth 0 s 0 <> 0 ->
    Zlength sg = 1 ->
    Znth 0 sg 0 = 0 ->
    EditZeroFull n cnt0 ->
    EditZeroFull n cnt1 ->
    EditBuildState s t n 1 sg cnt0
      (replace_Znth 0 (Znth 0 cnt1 0 + 1) cnt1).
Proof.
  intros s t n sg cnt0 cnt1 Hn Hslen Htlen Hsbits Htbits Hs0nz Hsglen Hsgzero Hcnt0 Hcnt1.
  unfold EditBuildState.
  split; [lia|].
  split.
  - eapply EditBinaryList_from_bounds__zeroing_and_base_build; eauto.
  - split.
    + eapply EditBinaryList_from_bounds__zeroing_and_base_build; eauto.
    + split.
      * eapply EditSegmentPrefix_one_zero__zeroing_and_base_build; eauto.
      * eapply EditCountsForPrefix_initial_one__zeroing_and_base_build; eauto.
Qed.
Lemma EditBuildState_initial_s1_zero__zeroing_and_base_build :
  forall s t n sg cnt0 cnt1,
    1 <= n ->
    Zlength s = n ->
    Zlength t = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx t 0 <= 1) ->
    Znth 0 s 0 = 0 ->
    Zlength sg = 1 ->
    Znth 0 sg 0 = 0 ->
    EditZeroFull n cnt0 ->
    EditZeroFull n cnt1 ->
    EditBuildState s t n 1 sg
      (replace_Znth 0 (Znth 0 cnt0 0 + 1) cnt0) cnt1.
Proof.
  intros s t n sg cnt0 cnt1 Hn Hslen Htlen Hsbits Htbits Hs0zero Hsglen Hsgzero Hcnt0 Hcnt1.
  unfold EditBuildState.
  split; [lia|].
  split.
  - eapply EditBinaryList_from_bounds__zeroing_and_base_build; eauto.
  - split.
    + eapply EditBinaryList_from_bounds__zeroing_and_base_build; eauto.
    + split.
      * eapply EditSegmentPrefix_one_zero__zeroing_and_base_build; eauto.
      * eapply EditCountsForPrefix_initial_zero__zeroing_and_base_build; eauto.
Qed.
Lemma edit_zrange_between_in__build_s1_segments_counts :
  forall lo hi k,
    lo <= hi ->
    In k (edit_zrange_between lo hi) <-> lo <= k < hi.
Proof.
  intros lo hi k Hle.
  unfold edit_zrange_between.
  split.
  - intros Hin.
    apply in_map_iff in Hin.
    destruct Hin as [off [Hk Hoff]].
    apply in_seq in Hoff.
    lia.
  - intros Hk.
    apply in_map_iff.
    exists (Z.to_nat (k - lo)).
    split.
    + lia.
    + apply in_seq. lia.
Qed.
Lemma edit_edge_openb_true_iff__build_s1_segments_counts :
  forall t idx,
    edit_edge_openb t idx = true <-> edit_edge_open t idx.
Proof.
  intros t idx.
  unfold edit_edge_openb, edit_edge_open.
  rewrite andb_true_iff, !Z.eqb_eq.
  tauto.
Qed.
Lemma edit_all_edges_openb_true_iff__build_s1_segments_counts :
  forall t lo hi,
    lo <= hi ->
    edit_all_edges_openb t lo hi = true <->
    forall k, lo <= k < hi -> edit_edge_open t k.
Proof.
  intros t lo hi Hle.
  unfold edit_all_edges_openb.
  rewrite forallb_forall.
  split.
  - intros Hall k Hk.
    apply edit_edge_openb_true_iff__build_s1_segments_counts.
    apply Hall.
    apply edit_zrange_between_in__build_s1_segments_counts; lia.
  - intros Hall k Hk.
    apply edit_edge_openb_true_iff__build_s1_segments_counts.
    apply Hall.
    apply edit_zrange_between_in__build_s1_segments_counts in Hk; lia.
Qed.
Lemma edit_block_startb_true_iff__build_s1_segments_counts :
  forall t idx start,
    edit_block_startb t idx start = true <-> EditBlockStart t idx start.
Proof.
  intros t idx start.
  unfold edit_block_startb, EditBlockStart.
  split.
  - intros Hb.
    apply andb_true_iff in Hb as [Hb Hlast].
    apply andb_true_iff in Hb as [Hb Hall].
    apply andb_true_iff in Hb as [Hstart0 Hstartidx].
    apply Z.leb_le in Hstart0.
    apply Z.leb_le in Hstartidx.
    split; [lia|].
    split.
    + intros k Hk.
      pose proof
        (proj1 (edit_all_edges_openb_true_iff__build_s1_segments_counts
                  t (start + 1) (idx + 1) ltac:(lia)) Hall) as HallP.
      apply HallP. lia.
    + apply orb_true_iff in Hlast.
      destruct Hlast as [Hzero | Hnot].
      * left. apply Z.eqb_eq in Hzero. lia.
      * apply negb_true_iff in Hnot.
        right. intros Hedge.
        apply edit_edge_openb_true_iff__build_s1_segments_counts in Hedge.
        congruence.
  - intros [[Hstart0 Hstartidx] [Hedges Hlast]].
    apply andb_true_iff.
    split.
    + apply andb_true_iff.
      split.
      * apply andb_true_iff.
        split; apply Z.leb_le; lia.
      * apply edit_all_edges_openb_true_iff__build_s1_segments_counts; try lia.
        intros k Hk. apply Hedges. lia.
    + apply orb_true_iff.
      destruct Hlast as [Hzero | Hnot].
      * left. apply Z.eqb_eq. lia.
      * right.
        apply negb_true_iff.
        destruct (edit_edge_openb t start) eqn:Hedge; auto.
        apply edit_edge_openb_true_iff__build_s1_segments_counts in Hedge.
        contradiction.
Qed.
Lemma EditBlockStart_unique__build_s1_segments_counts :
  forall t idx a b,
    EditBlockStart t idx a ->
    EditBlockStart t idx b ->
    a = b.
Proof.
  intros t idx a b Ha Hb.
  destruct Ha as [[Ha0 Haidx] [Haedge Haend]].
  destruct Hb as [[Hb0 Hbidx] [Hbedge Hbend]].
  destruct (Z_lt_ge_dec a b) as [Hlt | Hge].
  - assert (edit_edge_open t b) as Hedge by (apply Haedge; lia).
    destruct Hbend as [-> | Hnot]; lia || contradiction.
  - destruct (Z_lt_ge_dec b a) as [Hgt | Hle]; [|lia].
    assert (edit_edge_open t a) as Hedge by (apply Hbedge; lia).
    destruct Haend as [-> | Hnot]; lia || contradiction.
Qed.
Lemma edit_zrange_in__build_s1_segments_counts :
  forall n k,
    0 <= n ->
    In k (edit_zrange n) <-> 0 <= k < n.
Proof.
  intros n k Hn.
  unfold edit_zrange.
  split.
  - intros Hin.
    apply in_map_iff in Hin.
    destruct Hin as [off [Hk Hoff]].
    apply in_seq in Hoff.
    lia.
  - intros Hk.
    apply in_map_iff.
    exists (Z.to_nat k).
    split; [lia|].
    apply in_seq. lia.
Qed.
Lemma edit_zrange_NoDup__build_s1_segments_counts :
  forall n,
    NoDup (edit_zrange n).
Proof.
  intros n.
  unfold edit_zrange.
  remember (seq 0 (Z.to_nat n)) as xs.
  assert (NoDup xs) as Hnodup by (subst xs; apply seq_NoDup).
  clear Heqxs.
  induction Hnodup as [|x xs Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intros Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hin]].
      apply Hnotin.
      replace x with y by lia.
      exact Hin.
    + exact IH.
Qed.
Lemma filter_limit_succ_once__build_s1_segments_counts :
  forall xs i (Q : Z -> bool),
    NoDup xs ->
    In i xs ->
    (forall x, In x xs -> x < i \/ x = i \/ i < x) ->
    length (List.filter (fun idx => andb (Z.ltb idx (i + 1)) (Q idx)) xs) =
    (length (List.filter (fun idx => andb (Z.ltb idx i) (Q idx)) xs) +
     (if Q i then 1%nat else 0%nat))%nat.
Proof.
  intros xs i Q Hnodup Hin Htri.
  induction xs as [|x xs IH]; simpl in *.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct Hin as [Hx | Hinxs].
    + subst x.
      rewrite Z.ltb_irrefl.
      replace (Z.ltb i (i + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Q i); simpl.
      * assert (Hfeq :
          List.filter (fun idx : Z => andb (Z.ltb idx (i + 1)) (Q idx)) xs =
          List.filter (fun idx : Z => andb (Z.ltb idx i) (Q idx)) xs).
        {
          apply filter_ext_in.
          intros y Hy.
          pose proof (Htri y (or_intror Hy)) as [Hlt | [Heq | Hgt]].
          - replace (Z.ltb y (i + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
            replace (Z.ltb y i) with true by (symmetry; apply Z.ltb_lt; lia).
            reflexivity.
          - subst y. contradiction.
          - replace (Z.ltb y (i + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
            replace (Z.ltb y i) with false by (symmetry; apply Z.ltb_ge; lia).
            reflexivity.
        }
        rewrite Hfeq. lia.
      * assert (Hfeq :
          List.filter (fun idx : Z => andb (Z.ltb idx (i + 1)) (Q idx)) xs =
          List.filter (fun idx : Z => andb (Z.ltb idx i) (Q idx)) xs).
        {
          apply filter_ext_in.
          intros y Hy.
          pose proof (Htri y (or_intror Hy)) as [Hlt | [Heq | Hgt]].
          - replace (Z.ltb y (i + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
            replace (Z.ltb y i) with true by (symmetry; apply Z.ltb_lt; lia).
            reflexivity.
          - subst y. contradiction.
          - replace (Z.ltb y (i + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
            replace (Z.ltb y i) with false by (symmetry; apply Z.ltb_ge; lia).
            reflexivity.
        }
        rewrite Hfeq. lia.
    + specialize (IH Hnodup' Hinxs ltac:(intros y Hy; apply Htri; right; exact Hy)).
      destruct (Z.eq_dec x i) as [->|Hne]; [contradiction|].
      pose proof (Htri x (or_introl eq_refl)) as [Hlt | [Heq | Hgt]]; [|contradiction|].
      * replace (Z.ltb x (i + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (Z.ltb x i) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Q x); simpl; rewrite IH; lia.
      * replace (Z.ltb x (i + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (Z.ltb x i) with false by (symmetry; apply Z.ltb_ge; lia).
        exact IH.
Qed.
Lemma NoDup_filter_bool__build_s1_segments_counts :
  forall (A : Type) (p : A -> bool) xs,
    NoDup xs -> NoDup (List.filter p xs).
Proof.
  intros A p xs Hnodup.
  induction Hnodup as [|x xs Hnotin Hnodup IH]; simpl.
  - constructor.
  - destruct (p x) eqn:Hpx.
    + constructor.
      * intros Hin.
        apply filter_In in Hin.
        tauto.
      * exact IH.
    + exact IH.
Qed.
Lemma NoDup_zlist_range_length__build_s1_segments_counts :
  forall limit picks,
    0 <= limit ->
    NoDup picks ->
    Forall (fun i => 0 <= i < limit) picks ->
    Z.of_nat (length picks) <= limit.
Proof.
  intros limit picks Hlimit Hnodup Hforall.
  assert (Hin_range : incl picks (edit_zrange limit)).
  {
    intros x Hx.
    apply edit_zrange_in__build_s1_segments_counts; auto.
    apply Forall_forall with (x := x) in Hforall; auto.
  }
  pose proof (NoDup_incl_length Hnodup Hin_range) as Hlen.
  unfold edit_zrange in Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.
Lemma edit_count_bit_in_block_prefix_bound__build_s1_segments_counts :
  forall s t limit block bit,
    0 <= limit <= Zlength s ->
    0 <= edit_count_bit_in_block_prefix s t limit block bit <= limit.
Proof.
  intros s t limit block bit Hlimit.
  unfold edit_count_bit_in_block_prefix.
  change
    (0 <=
     Z.of_nat
       (length
          (List.filter
             (fun idx : Z =>
                andb (andb (Z.ltb idx limit) (edit_block_startb t idx block))
                  (edit_bit_atb s idx bit))
             (edit_zrange (Zlength s)))) <= limit).
  split; [lia|].
  apply NoDup_zlist_range_length__build_s1_segments_counts.
  - lia.
  - apply NoDup_filter_bool__build_s1_segments_counts.
    apply edit_zrange_NoDup__build_s1_segments_counts.
  - apply Forall_forall.
    intros idx Hin.
    apply filter_In in Hin.
    destruct Hin as [HinRange Hpred].
    apply edit_zrange_in__build_s1_segments_counts in HinRange.
    + destruct (Z.ltb idx limit) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt.
      lia.
    + apply Zlength_nonneg.
Qed.
Lemma edit_count_bit_in_block_prefix_succ__build_s1_segments_counts :
  forall s t i block bit,
    0 <= i < Zlength s ->
    edit_count_bit_in_block_prefix s t (i + 1) block bit =
    edit_count_bit_in_block_prefix s t i block bit +
    (if andb (edit_block_startb t i block) (edit_bit_atb s i bit) then 1 else 0).
Proof.
  intros s t i block bit Hi.
  unfold edit_count_bit_in_block_prefix.
  change
    (Z.of_nat
       (length
          (List.filter
             (fun idx : Z =>
                andb (andb (Z.ltb idx (i + 1)) (edit_block_startb t idx block))
                  (edit_bit_atb s idx bit))
             (edit_zrange (Zlength s)))) =
     Z.of_nat
       (length
          (List.filter
             (fun idx : Z =>
                andb (andb (Z.ltb idx i) (edit_block_startb t idx block))
                  (edit_bit_atb s idx bit))
             (edit_zrange (Zlength s)))) +
     (if andb (edit_block_startb t i block) (edit_bit_atb s i bit) then 1 else 0)).
  assert (Hf_succ :
    List.filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx (i + 1)) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit))
      (edit_zrange (Zlength s)) =
    List.filter
      (fun idx : Z =>
         andb (Z.ltb idx (i + 1))
           (andb (edit_block_startb t idx block) (edit_bit_atb s idx bit)))
      (edit_zrange (Zlength s))).
  {
    apply filter_ext_in.
    intros idx _.
    rewrite andb_assoc.
    reflexivity.
  }
  assert (Hf_prev :
    List.filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx i) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit))
      (edit_zrange (Zlength s)) =
    List.filter
      (fun idx : Z =>
         andb (Z.ltb idx i)
           (andb (edit_block_startb t idx block) (edit_bit_atb s idx bit)))
      (edit_zrange (Zlength s))).
  {
    apply filter_ext_in.
    intros idx _.
    rewrite andb_assoc.
    reflexivity.
  }
  rewrite Hf_succ, Hf_prev.
  rewrite (filter_limit_succ_once__build_s1_segments_counts
             (edit_zrange (Zlength s)) i
             (fun idx => andb (edit_block_startb t idx block) (edit_bit_atb s idx bit))).
  - rewrite Nat2Z.inj_add.
    destruct (andb (edit_block_startb t i block) (edit_bit_atb s i bit)); lia.
  - apply edit_zrange_NoDup__build_s1_segments_counts.
  - apply edit_zrange_in__build_s1_segments_counts; [apply Zlength_nonneg|lia].
  - intros x Hx.
    apply edit_zrange_in__build_s1_segments_counts in Hx; [lia|apply Zlength_nonneg].
Qed.
Lemma edit_snoc_Znth_last__build_s1_segments_counts :
  forall (xs : list Z) i x d,
    Zlength xs = i ->
    0 <= i ->
    Znth i (xs ++ x :: nil) d = x.
Proof.
  intros xs i x d Hlen Hi.
  rewrite app_Znth2 by lia.
  replace (i - Zlength xs) with 0 by lia.
  simpl.
  reflexivity.
Qed.
Lemma EditSegmentPrefix_extend_new__build_s1_segments_counts :
  forall t i sg,
    EditSegmentPrefix t i sg ->
    0 <= i ->
    ~ edit_edge_open t i ->
    EditSegmentPrefix t (i + 1) (sg ++ i :: nil).
Proof.
  intros t i sg Hseg Hi Hclosed.
  destruct Hseg as [Hlen Hstarts].
  split.
  - rewrite Zlength_app_cons. lia.
  - intros idx Hidx.
    destruct (Z.eq_dec idx i) as [->|Hne].
    + rewrite app_Znth2 by lia.
      replace (i - Zlength sg) with 0 by lia.
      change (Znth 0 (i :: nil) 0) with i.
      unfold EditBlockStart.
      split; [lia|].
      split.
      * intros k Hk. lia.
      * right. exact Hclosed.
    + rewrite app_Znth1 by lia.
      apply Hstarts. lia.
Qed.
Lemma EditSegmentPrefix_extend_open__build_s1_segments_counts :
  forall t i sg,
    EditSegmentPrefix t i sg ->
    1 <= i ->
    edit_edge_open t i ->
    EditSegmentPrefix t (i + 1) (sg ++ Znth (i - 1) sg 0 :: nil).
Proof.
  intros t i sg Hseg Hi Hedge.
  destruct Hseg as [Hlen Hstarts].
  split.
  - rewrite Zlength_app_cons. lia.
  - intros idx Hidx.
    destruct (Z.eq_dec idx i) as [->|Hne].
    + rewrite app_Znth2 by lia.
      replace (i - Zlength sg) with 0 by lia.
      change (Znth 0 (Znth (i - 1) sg 0 :: nil) 0) with (Znth (i - 1) sg 0).
      pose proof (Hstarts (i - 1) ltac:(lia)) as Hprev.
      destruct Hprev as [[Hb0 Hbidx] [Hedges Hlast]].
      unfold EditBlockStart.
      split; [lia|].
      split.
      * intros k Hk.
        destruct (Z.eq_dec k i) as [->|Hki].
        -- exact Hedge.
        -- apply Hedges. lia.
      * exact Hlast.
    + rewrite app_Znth1 by lia.
      apply Hstarts. lia.
Qed.
Lemma EditSegmentPrefix_last_block_bounds__build_s1_segments_counts :
  forall t i sg,
    EditSegmentPrefix t i sg ->
    1 <= i ->
    0 <= Znth (i - 1) sg 0 < i.
Proof.
  intros t i sg Hseg Hi.
  destruct Hseg as [_ Hstarts].
  pose proof (Hstarts (i - 1) ltac:(lia)) as Hblock.
  destruct Hblock as [[Hb0 Hbidx] _].
  lia.
Qed.
Lemma EditCountsForPrefix_extend_one__build_s1_segments_counts :
  forall s t n i sg cnt0 cnt1 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) sg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i sg 0 ->
    Znth i s 0 <> 0 ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    EditCountsForPrefix s t n (i + 1) cnt0
      (replace_Znth block (Znth block cnt1 0 + 1) cnt1).
Proof.
  intros s t n i sg cnt0 cnt1 block Hslen Hi Hseg Hcounts Hblock Hsnonzero Hsbin.
  destruct Hcounts as [Hlen0 [Hlen1 [Hcnt0 Hcnt1]]].
  assert (Hsone : Znth i s 0 = 1).
  { pose proof (Hsbin i ltac:(lia)); lia. }
  assert (Hstart : EditBlockStart t i block).
  {
    subst block.
    destruct Hseg as [_ Hstarts].
    apply Hstarts. lia.
  }
  assert (Hblock_range : 0 <= block < n).
  {
    destruct Hstart as [[Hb0 Hbidx] _].
    lia.
  }
  repeat split.
  - exact Hlen0.
  - rewrite Zlength_replace_Znth. exact Hlen1.
  - intros b Hb.
    rewrite Hcnt0 by lia.
    rewrite edit_count_bit_in_block_prefix_succ__build_s1_segments_counts
      by (rewrite Hslen; lia).
    unfold edit_bit_atb.
    replace (Z.eqb (Znth i s 0) 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    destruct (edit_block_startb t i b); simpl; lia.
  - intros b Hb.
    rewrite edit_count_bit_in_block_prefix_succ__build_s1_segments_counts
      by (rewrite Hslen; lia).
    destruct (Z.eq_dec b block) as [->|Hne].
    + rewrite Znth_replace_Znth_Same by (rewrite Hlen1; lia).
      rewrite Hcnt1 by lia.
      assert (Hstartb : edit_block_startb t i block = true).
      { apply edit_block_startb_true_iff__build_s1_segments_counts. exact Hstart. }
      unfold edit_bit_atb.
      replace (Z.eqb (Znth i s 0) 1) with true
        by (symmetry; apply Z.eqb_eq; lia).
      rewrite Hstartb. simpl. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hlen1; lia).
      rewrite Hcnt1 by lia.
      assert (Hstartb : edit_block_startb t i b = false).
      {
        destruct (edit_block_startb t i b) eqn:Hbstart; auto.
        apply edit_block_startb_true_iff__build_s1_segments_counts in Hbstart.
        pose proof (EditBlockStart_unique__build_s1_segments_counts
                      t i block b Hstart Hbstart).
        lia.
      }
      rewrite Hstartb. simpl. lia.
Qed.
Lemma EditCountsForPrefix_extend_zero__build_s1_segments_counts :
  forall s t n i sg cnt0 cnt1 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) sg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i sg 0 ->
    Znth i s 0 = 0 ->
    EditCountsForPrefix s t n (i + 1)
      (replace_Znth block (Znth block cnt0 0 + 1) cnt0) cnt1.
Proof.
  intros s t n i sg cnt0 cnt1 block Hslen Hi Hseg Hcounts Hblock Hszero.
  destruct Hcounts as [Hlen0 [Hlen1 [Hcnt0 Hcnt1]]].
  assert (Hstart : EditBlockStart t i block).
  {
    subst block.
    destruct Hseg as [_ Hstarts].
    apply Hstarts. lia.
  }
  assert (Hblock_range : 0 <= block < n).
  {
    destruct Hstart as [[Hb0 Hbidx] _].
    lia.
  }
  repeat split.
  - rewrite Zlength_replace_Znth. exact Hlen0.
  - exact Hlen1.
  - intros b Hb.
    rewrite edit_count_bit_in_block_prefix_succ__build_s1_segments_counts
      by (rewrite Hslen; lia).
    destruct (Z.eq_dec b block) as [->|Hne].
    + rewrite Znth_replace_Znth_Same by (rewrite Hlen0; lia).
      rewrite Hcnt0 by lia.
      assert (Hstartb : edit_block_startb t i block = true).
      { apply edit_block_startb_true_iff__build_s1_segments_counts. exact Hstart. }
      unfold edit_bit_atb.
      replace (Z.eqb (Znth i s 0) 0) with true
        by (symmetry; apply Z.eqb_eq; lia).
      rewrite Hstartb. simpl. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hlen0; lia).
      rewrite Hcnt0 by lia.
      assert (Hstartb : edit_block_startb t i b = false).
      {
        destruct (edit_block_startb t i b) eqn:Hbstart; auto.
        apply edit_block_startb_true_iff__build_s1_segments_counts in Hbstart.
        pose proof (EditBlockStart_unique__build_s1_segments_counts
                      t i block b Hstart Hbstart).
        lia.
      }
      rewrite Hstartb. simpl. lia.
  - intros b Hb.
    rewrite Hcnt1 by lia.
    rewrite edit_count_bit_in_block_prefix_succ__build_s1_segments_counts
      by (rewrite Hslen; lia).
    unfold edit_bit_atb.
    replace (Z.eqb (Znth i s 0) 1) with false
      by (symmetry; apply Z.eqb_neq; lia).
    destruct (edit_block_startb t i b); simpl; lia.
Qed.
Lemma EditScratchCountsBound_inc_second__build_s1_segments_counts :
  forall s t n i cnt0 cnt1 cnt20 cnt21 block,
    Zlength s = n ->
    0 <= i < n ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    0 <= block < n ->
    EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21 ->
    EditScratchCountsBound n cnt0
      (replace_Znth block (Znth block cnt1 0 + 1) cnt1) cnt20 cnt21.
Proof.
  intros s t n i cnt0 cnt1 cnt20 cnt21 block Hslen Hi Hcounts Hblock Hbounds.
  unfold EditScratchCountsBound, EditCountBounds in *.
  destruct Hbounds as [Hcnt0bd [Hcnt1bd [H20bd H21bd]]].
  destruct Hcnt0bd as [Hlen0 Hbd0].
  destruct Hcnt1bd as [Hlen1 Hbd1].
  destruct H20bd as [Hlen20 Hbd20].
  destruct H21bd as [Hlen21 Hbd21].
  split.
  - split; [exact Hlen0|exact Hbd0].
  - split.
    + split.
      * rewrite Zlength_replace_Znth. exact Hlen1.
      * intros idx Hidx.
        destruct (Z.eq_dec idx block) as [->|Hne].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hlen1; lia).
           destruct Hcounts as [_ [_ [_ Hcnt1]]].
           rewrite Hcnt1 by lia.
           pose proof (edit_count_bit_in_block_prefix_bound__build_s1_segments_counts
                         s t i block 1 ltac:(rewrite Hslen; lia)).
           lia.
        -- rewrite Znth_replace_Znth_Diff by (try rewrite Hlen1; lia).
           apply Hbd1. lia.
    + split.
      * split; [exact Hlen20|exact Hbd20].
      * split; [exact Hlen21|exact Hbd21].
Qed.
Lemma EditScratchCountsBound_inc_first__build_s1_segments_counts :
  forall s t n i cnt0 cnt1 cnt20 cnt21 block,
    Zlength s = n ->
    0 <= i < n ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    0 <= block < n ->
    EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21 ->
    EditScratchCountsBound n
      (replace_Znth block (Znth block cnt0 0 + 1) cnt0) cnt1 cnt20 cnt21.
Proof.
  intros s t n i cnt0 cnt1 cnt20 cnt21 block Hslen Hi Hcounts Hblock Hbounds.
  unfold EditScratchCountsBound, EditCountBounds in *.
  destruct Hbounds as [Hcnt0bd [Hcnt1bd [H20bd H21bd]]].
  destruct Hcnt0bd as [Hlen0 Hbd0].
  destruct Hcnt1bd as [Hlen1 Hbd1].
  destruct H20bd as [Hlen20 Hbd20].
  destruct H21bd as [Hlen21 Hbd21].
  split.
  - split.
    + rewrite Zlength_replace_Znth. exact Hlen0.
    + intros idx Hidx.
      destruct (Z.eq_dec idx block) as [->|Hne].
      * rewrite Znth_replace_Znth_Same by (rewrite Hlen0; lia).
        destruct Hcounts as [_ [_ [Hcnt0 _]]].
        rewrite Hcnt0 by lia.
        pose proof (edit_count_bit_in_block_prefix_bound__build_s1_segments_counts
                      s t i block 0 ltac:(rewrite Hslen; lia)).
        lia.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hlen0; lia).
        apply Hbd0. lia.
  - split.
    + split; [exact Hlen1|exact Hbd1].
    + split.
      * split; [exact Hlen20|exact Hbd20].
      * split; [exact Hlen21|exact Hbd21].
Qed.
Lemma EditBuildState_extend_one__build_s1_segments_counts :
  forall s t n i sg cnt0 cnt1 block,
    Zlength s = n ->
    Zlength t = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx t 0 <= 1) ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) sg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i sg 0 ->
    Znth i s 0 <> 0 ->
    EditBuildState s t n (i + 1) sg cnt0
      (replace_Znth block (Znth block cnt1 0 + 1) cnt1).
Proof.
  intros s t n i sg cnt0 cnt1 block Hslen Htlen Hsbin Htbin Hi Hseg Hcounts Hblock Hsnonzero.
  unfold EditBuildState, EditBinaryList.
  split; [lia|].
  split.
  - split.
    + exact Hslen.
    + intros idx Hidx. pose proof (Hsbin idx Hidx). lia.
  - split.
    + split.
      * exact Htlen.
      * intros idx Hidx. pose proof (Htbin idx Hidx). lia.
    + split.
      * exact Hseg.
      * eapply EditCountsForPrefix_extend_one__build_s1_segments_counts; eauto.
Qed.
Lemma EditBuildState_extend_zero__build_s1_segments_counts :
  forall s t n i sg cnt0 cnt1 block,
    Zlength s = n ->
    Zlength t = n ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx t 0 <= 1) ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) sg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i sg 0 ->
    Znth i s 0 = 0 ->
    EditBuildState s t n (i + 1) sg
      (replace_Znth block (Znth block cnt0 0 + 1) cnt0) cnt1.
Proof.
  intros s t n i sg cnt0 cnt1 block Hslen Htlen Hsbin Htbin Hi Hseg Hcounts Hblock Hszero.
  unfold EditBuildState, EditBinaryList.
  split; [lia|].
  split.
  - split.
    + exact Hslen.
    + intros idx Hidx. pose proof (Hsbin idx Hidx). lia.
  - split.
    + split.
      * exact Htlen.
      * intros idx Hidx. pose proof (Htbin idx Hidx). lia.
    + split.
      * exact Hseg.
      * eapply EditCountsForPrefix_extend_zero__build_s1_segments_counts; eauto.
Qed.
Lemma edit_seq_add__build_s2_segments_counts :
  forall start len,
    seq start len = map (fun off => (start + off)%nat) (seq 0 len).
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start; simpl; auto.
  f_equal.
  - lia.
  - rewrite <- (seq_shift len 0).
    rewrite map_map.
    replace (map (fun x : nat => (start + S x)%nat) (seq 0 len))
      with (map (fun off : nat => (S start + off)%nat) (seq 0 len)).
    + apply IH.
    + apply map_ext. intros off. lia.
Qed.
Lemma edit_zrange_between_cons__build_s2_segments_counts :
  forall lo hi,
    lo < hi ->
    edit_zrange_between lo hi =
      lo :: edit_zrange_between (lo + 1) hi.
Proof.
  intros lo hi Hlt.
  unfold edit_zrange_between.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  replace (lo + 0) with lo by lia.
  f_equal.
  rewrite <- (seq_shift (Z.to_nat (hi - (lo + 1))) 0).
  rewrite map_map.
  apply map_ext.
  intros off.
  simpl.
  lia.
Qed.
Lemma edit_zrange_split__build_s2_segments_counts :
  forall n i,
    0 <= i < n ->
    edit_zrange n =
      edit_zrange i ++ i :: edit_zrange_between (i + 1) n.
Proof.
  intros n i Hi.
  unfold edit_zrange, edit_zrange_between.
  replace (Z.to_nat n) with (Z.to_nat i + S (Z.to_nat (n - (i + 1))))%nat by lia.
  rewrite seq_app.
  rewrite map_app.
  f_equal.
  simpl.
  f_equal.
  - lia.
  - rewrite edit_seq_add__build_s2_segments_counts.
    rewrite map_map.
    apply map_ext.
    intros off.
    simpl.
    lia.
Qed.
Lemma edit_zrange_In__build_s2_segments_counts :
  forall n idx,
    In idx (edit_zrange n) ->
    0 <= idx < n.
Proof.
  intros n idx Hin.
  unfold edit_zrange in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [off [Hidx Hin]].
  apply in_seq in Hin.
  subst idx.
  lia.
Qed.
Lemma edit_zrange_between_In__build_s2_segments_counts :
  forall lo hi idx,
    In idx (edit_zrange_between lo hi) ->
    lo <= idx < hi.
Proof.
  intros lo hi idx Hin.
  unfold edit_zrange_between in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [off [Hidx Hin]].
  apply in_seq in Hin.
  subst idx.
  lia.
Qed.
Lemma edit_filter_all_false__build_s2_segments_counts :
  forall {A : Type} (f : A -> bool) (xs : list A),
    (forall x, In x xs -> f x = false) ->
    filter f xs = nil.
Proof.
  intros A f xs Hall.
  induction xs as [|x xs IH]; simpl; auto.
  rewrite (Hall x (or_introl eq_refl)).
  apply IH.
  intros y Hy.
  apply Hall.
  simpl; auto.
Qed.
Lemma edit_count_bit_in_block_prefix_succ__build_s2_segments_counts :
  forall s t n i block bit,
    Zlength s = n ->
    0 <= i < n ->
    edit_count_bit_in_block_prefix s t (i + 1) block bit =
    edit_count_bit_in_block_prefix s t i block bit +
      (if andb (edit_block_startb t i block) (edit_bit_atb s i bit) then 1 else 0).
Proof.
  intros s t n i block bit Hlen Hi.
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  rewrite (edit_zrange_split__build_s2_segments_counts n i Hi).
  repeat rewrite filter_app.
  simpl.
  assert (Hprefix:
    filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx (i + 1)) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit)) (edit_zrange i) =
    filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx i) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit)) (edit_zrange i)).
  {
    apply filter_ext_in.
    intros idx Hin.
    pose proof (edit_zrange_In__build_s2_segments_counts i idx Hin) as Hidx.
    destruct (Z.ltb_spec idx (i + 1));
      destruct (Z.ltb_spec idx i); try lia; reflexivity.
  }
  rewrite Hprefix.
  assert (Htail_new:
    filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx (i + 1)) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit))
      (edit_zrange_between (i + 1) n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts (i + 1) n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx (i + 1)); try lia; reflexivity.
  }
  assert (Htail_old:
    filter
      (fun idx : Z =>
         andb (andb (Z.ltb idx i) (edit_block_startb t idx block))
           (edit_bit_atb s idx bit))
      (edit_zrange_between (i + 1) n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts (i + 1) n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx i); try lia; reflexivity.
  }
  rewrite Htail_new, Htail_old.
  repeat rewrite app_nil_r.
  destruct (Z.ltb_spec i (i + 1)); [|lia].
  destruct (Z.ltb_spec i i); [lia|].
  repeat rewrite app_nil_r.
  rewrite length_app.
  destruct (edit_block_startb t i block && edit_bit_atb s i bit) eqn:Hmatch; simpl.
  - rewrite Nat2Z.inj_add. rewrite Hmatch. simpl. reflexivity.
  - rewrite Hmatch. rewrite Nat2Z.inj_add. simpl. reflexivity.
Qed.
Lemma edit_block_startb_zero__build_s2_segments_counts :
  forall t block,
    edit_block_startb t 0 block = Z.eqb block 0.
Proof.
  intros t block.
  unfold edit_block_startb, edit_all_edges_openb, edit_zrange_between.
  simpl.
  destruct (Z.eq_dec block 0) as [Heq | Hneq].
  - subst block. reflexivity.
  - destruct (Z.leb_spec0 0 block);
      destruct (Z.leb_spec0 block 0); try lia; reflexivity.
Qed.
Lemma edit_count_prefix_one_nonzero_zero_bit__build_s2_segments_counts :
  forall s t n block,
    Zlength s = n ->
    1 <= n ->
    Znth 0 s 0 <> 0 ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    edit_count_bit_in_block_prefix s t 1 block 0 = 0.
Proof.
  intros s t n block Hlen Hn Hs0_ne Hbin.
  assert (Hs0 : Znth 0 s 0 = 1).
  {
    specialize (Hbin 0 ltac:(lia)).
    lia.
  }
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  rewrite (edit_zrange_split__build_s2_segments_counts n 0) by lia.
  repeat rewrite filter_app.
  simpl.
  assert (Htail:
    filter
      (fun idx : Z =>
         Z.ltb idx 1 && edit_block_startb t idx block && edit_bit_atb s idx 0)
      (edit_zrange_between 1 n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts 1 n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx 1); try lia; reflexivity.
  }
  rewrite Htail.
  repeat rewrite app_nil_r.
  unfold edit_zrange.
  simpl.
  unfold edit_bit_atb.
  rewrite Hs0.
  simpl.
  destruct (edit_block_startb t 0 block); reflexivity.
Qed.
Lemma edit_count_prefix_one_nonzero_one_bit__build_s2_segments_counts :
  forall s t n block,
    Zlength s = n ->
    1 <= n ->
    Znth 0 s 0 <> 0 ->
    (forall idx, 0 <= idx < n -> 0 <= Znth idx s 0 <= 1) ->
    edit_count_bit_in_block_prefix s t 1 block 1 =
      (if Z.eqb block 0 then 1 else 0).
Proof.
  intros s t n block Hlen Hn Hs0_ne Hbin.
  assert (Hs0 : Znth 0 s 0 = 1).
  {
    specialize (Hbin 0 ltac:(lia)).
    lia.
  }
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  rewrite (edit_zrange_split__build_s2_segments_counts n 0) by lia.
  repeat rewrite filter_app.
  simpl.
  assert (Htail:
    filter
      (fun idx : Z =>
         Z.ltb idx 1 && edit_block_startb t idx block && edit_bit_atb s idx 1)
      (edit_zrange_between 1 n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts 1 n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx 1); try lia; reflexivity.
  }
  rewrite Htail.
  repeat rewrite app_nil_r.
  unfold edit_zrange.
  simpl.
  unfold edit_bit_atb.
  rewrite Hs0.
  simpl.
  rewrite edit_block_startb_zero__build_s2_segments_counts.
  destruct (Z.eqb block 0); reflexivity.
Qed.
Lemma edit_count_prefix_one_zero_zero_bit__build_s2_segments_counts :
  forall s t n block,
    Zlength s = n ->
    1 <= n ->
    Znth 0 s 0 = 0 ->
    edit_count_bit_in_block_prefix s t 1 block 0 =
      (if Z.eqb block 0 then 1 else 0).
Proof.
  intros s t n block Hlen Hn Hs0.
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  rewrite (edit_zrange_split__build_s2_segments_counts n 0) by lia.
  repeat rewrite filter_app.
  simpl.
  assert (Htail:
    filter
      (fun idx : Z =>
         Z.ltb idx 1 && edit_block_startb t idx block && edit_bit_atb s idx 0)
      (edit_zrange_between 1 n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts 1 n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx 1); try lia; reflexivity.
  }
  rewrite Htail.
  repeat rewrite app_nil_r.
  unfold edit_zrange.
  simpl.
  unfold edit_bit_atb.
  rewrite Hs0.
  simpl.
  rewrite edit_block_startb_zero__build_s2_segments_counts.
  destruct (Z.eqb block 0); reflexivity.
Qed.
Lemma edit_count_prefix_one_zero_one_bit__build_s2_segments_counts :
  forall s t n block,
    Zlength s = n ->
    1 <= n ->
    Znth 0 s 0 = 0 ->
    edit_count_bit_in_block_prefix s t 1 block 1 = 0.
Proof.
  intros s t n block Hlen Hn Hs0.
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  rewrite (edit_zrange_split__build_s2_segments_counts n 0) by lia.
  repeat rewrite filter_app.
  simpl.
  assert (Htail:
    filter
      (fun idx : Z =>
         Z.ltb idx 1 && edit_block_startb t idx block && edit_bit_atb s idx 1)
      (edit_zrange_between 1 n) = nil).
  {
    apply edit_filter_all_false__build_s2_segments_counts.
    intros idx Hin.
    pose proof (edit_zrange_between_In__build_s2_segments_counts 1 n idx Hin) as Hidx.
    destruct (Z.ltb_spec idx 1); try lia; reflexivity.
  }
  rewrite Htail.
  repeat rewrite app_nil_r.
  unfold edit_zrange.
  simpl.
  unfold edit_bit_atb.
  rewrite Hs0.
  simpl.
  destruct (edit_block_startb t 0 block); reflexivity.
Qed.
Lemma edit_zrange_between_In_iff__build_s2_segments_counts :
  forall lo hi idx,
    In idx (edit_zrange_between lo hi) <-> lo <= idx < hi.
Proof.
  intros lo hi idx.
  split.
  - apply edit_zrange_between_In__build_s2_segments_counts.
  - intros Hrange.
    unfold edit_zrange_between.
    apply in_map_iff.
    exists (Z.to_nat (idx - lo)).
    split.
    + rewrite Z2Nat.id by lia.
      lia.
    + apply in_seq.
      split; [lia|].
      apply Z2Nat.inj_lt; lia.
Qed.
Lemma edit_edge_openb_true_iff__build_s2_segments_counts :
  forall t idx,
    edit_edge_openb t idx = true <-> edit_edge_open t idx.
Proof.
  intros t idx.
  unfold edit_edge_openb, edit_edge_open.
  split.
  - intros H.
    apply andb_true_iff in H.
    destruct H as [Hprev Hcur].
    apply Z.eqb_eq in Hprev.
    apply Z.eqb_eq in Hcur.
    split; assumption.
  - intros [Hprev Hcur].
    rewrite Hprev, Hcur.
    reflexivity.
Qed.
Lemma edit_all_edges_openb_true_iff__build_s2_segments_counts :
  forall t lo hi,
    edit_all_edges_openb t lo hi = true <->
    forall k, lo <= k < hi -> edit_edge_open t k.
Proof.
  intros t lo hi.
  unfold edit_all_edges_openb.
  split.
  - intros Hall k Hrange.
    apply forallb_forall with (x := k) in Hall.
    + apply (proj1 (edit_edge_openb_true_iff__build_s2_segments_counts t k)).
      exact Hall.
    + apply (proj2 (edit_zrange_between_In_iff__build_s2_segments_counts lo hi k)).
      exact Hrange.
  - intros Hall.
    apply forallb_forall.
    intros k Hin.
    apply (proj2 (edit_edge_openb_true_iff__build_s2_segments_counts t k)).
    apply Hall.
    apply edit_zrange_between_In__build_s2_segments_counts.
    exact Hin.
Qed.
Lemma edit_block_startb_true_iff__build_s2_segments_counts :
  forall t idx start,
    edit_block_startb t idx start = true <->
    EditBlockStart t idx start.
Proof.
  intros t idx start.
  unfold edit_block_startb, EditBlockStart.
  split.
  - intros H.
    repeat rewrite andb_true_iff in H.
    destruct H as [[[Hlo Hhi] Hedges] Hstart].
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    pose proof
      (proj1 (edit_all_edges_openb_true_iff__build_s2_segments_counts
        t (start + 1) (idx + 1)) Hedges) as Hedges_prop.
    apply orb_true_iff in Hstart.
    split; [lia|].
    split.
    + intros k Hk.
      apply Hedges_prop.
      lia.
    + destruct Hstart as [Hzero | Hnot].
      * left. apply Z.eqb_eq in Hzero. exact Hzero.
      * right.
        apply negb_true_iff in Hnot.
        intro Hedge.
        apply (proj2 (edit_edge_openb_true_iff__build_s2_segments_counts
          t start)) in Hedge.
        rewrite Hedge in Hnot.
        discriminate.
  - intros [[Hlo Hhi] [Hedges Hstart]].
    repeat rewrite andb_true_iff.
    split.
    + split.
      * split.
        -- apply Z.leb_le. lia.
        -- apply Z.leb_le. lia.
      * apply (proj2 (edit_all_edges_openb_true_iff__build_s2_segments_counts
          t (start + 1) (idx + 1))).
        intros k Hk.
        apply Hedges.
        lia.
    + apply orb_true_iff.
      destruct Hstart as [Hzero | Hnot].
      * left. apply Z.eqb_eq. exact Hzero.
      * right. apply negb_true_iff.
        destruct (edit_edge_openb t start) eqn:Hedge; [|reflexivity].
        apply (proj1 (edit_edge_openb_true_iff__build_s2_segments_counts
          t start)) in Hedge.
        contradiction.
Qed.
Lemma edit_block_start_unique__build_s2_segments_counts :
  forall t idx start1 start2,
    EditBlockStart t idx start1 ->
    EditBlockStart t idx start2 ->
    start1 = start2.
Proof.
  intros t idx start1 start2 Hs1 Hs2.
  destruct Hs1 as [[Hs1_lo Hs1_hi] [Hs1_edges Hs1_start]].
  destruct Hs2 as [[Hs2_lo Hs2_hi] [Hs2_edges Hs2_start]].
  destruct (Z_lt_dec start1 start2) as [Hlt | Hnlt].
  - assert (edit_edge_open t start2) as Hedge.
    {
      apply Hs1_edges.
      lia.
    }
    destruct Hs2_start as [Hzero | Hnot].
    + lia.
    + contradiction.
  - destruct (Z_lt_dec start2 start1) as [Hlt | Hnlt2].
    + assert (edit_edge_open t start1) as Hedge.
      {
        apply Hs2_edges.
        lia.
      }
      destruct Hs1_start as [Hzero | Hnot].
      * lia.
      * contradiction.
    + lia.
Qed.
Lemma edit_block_startb_unique__build_s2_segments_counts :
  forall t idx start block,
    EditBlockStart t idx start ->
    edit_block_startb t idx block = true ->
    block = start.
Proof.
  intros t idx start block Hstart Hblock.
  apply (proj1 (edit_block_startb_true_iff__build_s2_segments_counts
    t idx block)) in Hblock.
  symmetry.
  eapply edit_block_start_unique__build_s2_segments_counts; eauto.
Qed.
Lemma edit_Znth_app_last__build_s2_segments_counts :
  forall {A : Type} (xs : list A) (v d : A) i,
    Zlength xs = i ->
    Znth i (xs ++ v :: nil) d = v.
Proof.
  intros A xs v d i Hlen.
  rewrite app_Znth2 by lia.
  replace (i - Zlength xs) with 0 by lia.
  reflexivity.
Qed.
Lemma edit_segment_prefix_append_new__build_s2_segments_counts :
  forall t i sg,
    EditSegmentPrefix t i sg ->
    0 <= i ->
    ~ edit_edge_open t i ->
    EditSegmentPrefix t (i + 1) (sg ++ i :: nil).
Proof.
  intros t i sg Hseg Hi Hclosed.
  unfold EditSegmentPrefix in *.
  destruct Hseg as [Hlen Hseg].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros idx Hidx.
    destruct (Z.eq_dec idx i) as [Heq | Hneq].
    + subst idx.
      rewrite edit_Znth_app_last__build_s2_segments_counts by exact Hlen.
      unfold EditBlockStart.
      split; [lia|].
      split.
      * intros k Hk. lia.
      * destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
        -- left. exact Hi0.
        -- right. exact Hclosed.
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hseg.
      lia.
Qed.
Lemma edit_segment_prefix_append_same__build_s2_segments_counts :
  forall t i sg,
    EditSegmentPrefix t i sg ->
    1 <= i ->
    edit_edge_open t i ->
    EditSegmentPrefix t (i + 1) (sg ++ Znth (i - 1) sg 0 :: nil).
Proof.
  intros t i sg Hseg Hi Hedge.
  unfold EditSegmentPrefix in *.
  destruct Hseg as [Hlen Hseg].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros idx Hidx.
    destruct (Z.eq_dec idx i) as [Heq | Hneq].
    + subst idx.
      rewrite edit_Znth_app_last__build_s2_segments_counts by exact Hlen.
      specialize (Hseg (i - 1) ltac:(lia)).
      unfold EditBlockStart in *.
      destruct Hseg as [[Hlo Hhi] [Hedges Hstart]].
      split; [lia|].
      split.
      * intros k Hk.
        destruct (Z.eq_dec k i) as [Hki | Hki].
        -- subst k. exact Hedge.
        -- apply Hedges. lia.
      * exact Hstart.
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hseg.
      lia.
Qed.
Lemma edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts :
  forall s t n upto block bit,
    Zlength s = n ->
    0 <= n ->
    0 <= edit_count_bit_in_block_prefix s t upto block bit <= n.
Proof.
  intros s t n upto block bit Hlen Hn.
  unfold edit_count_bit_in_block_prefix.
  rewrite Hlen.
  split; [lia|].
  pose proof
    (filter_length_le
       (fun idx : Z =>
          Z.ltb idx upto && edit_block_startb t idx block &&
          edit_bit_atb s idx bit)
       (edit_zrange n)) as Hfilter.
  apply Nat2Z.inj_le in Hfilter.
  unfold edit_zrange in Hfilter.
  rewrite length_map in Hfilter.
  rewrite length_seq in Hfilter.
  rewrite Z2Nat.id in Hfilter by lia.
  exact Hfilter.
Qed.
Lemma edit_counts_prefix_extend_one__build_s2_segments_counts :
  forall s t n i seg cnt0 cnt1 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) seg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i seg 0 ->
    Znth i s 0 = 1 ->
    EditCountsForPrefix s t n (i + 1)
      cnt0 (replace_Znth block (Znth block cnt1 0 + 1) cnt1).
Proof.
  intros s t n i seg cnt0 cnt1 block Hslen Hi Hseg Hcnt Hblock Hbit.
  subst block.
  unfold EditCountsForPrefix in *.
  destruct Hcnt as [Hcnt0_len [Hcnt1_len [Hcnt0 Hcnt1]]].
  split; [exact Hcnt0_len|].
  split.
  - rewrite Zlength_replace_Znth. exact Hcnt1_len.
  - split.
    + intros block Hblock.
      rewrite Hcnt0 by exact Hblock.
      rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
        with (n := n); auto.
      unfold edit_bit_atb.
      rewrite Hbit.
      simpl.
      rewrite andb_false_r.
      lia.
    + intros block Hblock.
      pose proof Hseg as Hseg'.
      unfold EditSegmentPrefix in Hseg'.
      destruct Hseg' as [_ Hseg_prop].
      pose proof (Hseg_prop i ltac:(lia)) as Hstart_i.
      pose proof Hstart_i as Hstart_i_bool.
      apply (proj2 (edit_block_startb_true_iff__build_s2_segments_counts
        t i (Znth i seg 0))) in Hstart_i_bool.
      assert (0 <= Znth i seg 0 < n) as Hsegblock_bound.
      {
        pose proof Hstart_i as Hstart_i_bound.
        unfold EditBlockStart in Hstart_i_bound.
        destruct Hstart_i_bound as [[Hlo Hhi] _].
        lia.
      }
      destruct (Z.eq_dec block (Znth i seg 0)) as [Heq | Hneq].
      * subst block.
        rewrite Znth_replace_Znth_Same by (rewrite Hcnt1_len; exact Hblock).
        rewrite Hcnt1 by exact Hblock.
        rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
          with (n := n); auto.
        rewrite Hstart_i_bool.
        unfold edit_bit_atb.
        rewrite Hbit.
        simpl.
        lia.
      * rewrite Znth_replace_Znth_Diff
          by (try rewrite Hcnt1_len; try exact Hblock; try exact Hsegblock_bound; lia).
        rewrite Hcnt1 by exact Hblock.
        rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
          with (n := n); auto.
        assert (edit_block_startb t i block = false) as Hother.
        {
          destruct (edit_block_startb t i block) eqn:Hb; [|reflexivity].
          pose proof
            (edit_block_startb_unique__build_s2_segments_counts
               t i (Znth i seg 0) block Hstart_i Hb) as Hsame.
          contradiction.
        }
        rewrite Hother.
        simpl.
        lia.
Qed.
Lemma edit_counts_prefix_extend_zero__build_s2_segments_counts :
  forall s t n i seg cnt0 cnt1 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) seg ->
    EditCountsForPrefix s t n i cnt0 cnt1 ->
    block = Znth i seg 0 ->
    Znth i s 0 = 0 ->
    EditCountsForPrefix s t n (i + 1)
      (replace_Znth block (Znth block cnt0 0 + 1) cnt0) cnt1.
Proof.
  intros s t n i seg cnt0 cnt1 block Hslen Hi Hseg Hcnt Hblock Hbit.
  subst block.
  unfold EditCountsForPrefix in *.
  destruct Hcnt as [Hcnt0_len [Hcnt1_len [Hcnt0 Hcnt1]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hcnt0_len.
  - split; [exact Hcnt1_len|].
    split.
    + intros block Hblock.
      pose proof Hseg as Hseg'.
      unfold EditSegmentPrefix in Hseg'.
      destruct Hseg' as [_ Hseg_prop].
      pose proof (Hseg_prop i ltac:(lia)) as Hstart_i.
      pose proof Hstart_i as Hstart_i_bool.
      apply (proj2 (edit_block_startb_true_iff__build_s2_segments_counts
        t i (Znth i seg 0))) in Hstart_i_bool.
      assert (0 <= Znth i seg 0 < n) as Hsegblock_bound.
      {
        pose proof Hstart_i as Hstart_i_bound.
        unfold EditBlockStart in Hstart_i_bound.
        destruct Hstart_i_bound as [[Hlo Hhi] _].
        lia.
      }
      destruct (Z.eq_dec block (Znth i seg 0)) as [Heq | Hneq].
      * subst block.
        rewrite Znth_replace_Znth_Same by (rewrite Hcnt0_len; exact Hblock).
        rewrite Hcnt0 by exact Hblock.
        rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
          with (n := n); auto.
        rewrite Hstart_i_bool.
        unfold edit_bit_atb.
        rewrite Hbit.
        simpl.
        lia.
      * rewrite Znth_replace_Znth_Diff
          by (try rewrite Hcnt0_len; try exact Hblock; try exact Hsegblock_bound; lia).
        rewrite Hcnt0 by exact Hblock.
        rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
          with (n := n); auto.
        assert (edit_block_startb t i block = false) as Hother.
        {
          destruct (edit_block_startb t i block) eqn:Hb; [|reflexivity].
          pose proof
            (edit_block_startb_unique__build_s2_segments_counts
               t i (Znth i seg 0) block Hstart_i Hb) as Hsame.
          contradiction.
        }
        rewrite Hother.
        simpl.
        lia.
    + intros block Hblock.
      rewrite Hcnt1 by exact Hblock.
      rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
        with (n := n); auto.
      unfold edit_bit_atb.
      rewrite Hbit.
      simpl.
      rewrite andb_false_r.
      lia.
Qed.
Lemma edit_scratch_bound_update_one__build_s2_segments_counts :
  forall s t n i seg cnt10 cnt11 cnt20 cnt21 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) seg ->
    EditCountsForPrefix s t n i cnt20 cnt21 ->
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 ->
    block = Znth i seg 0 ->
    Znth i s 0 = 1 ->
    EditScratchCountsBound n cnt10 cnt11 cnt20
      (replace_Znth block (Znth block cnt21 0 + 1) cnt21).
Proof.
  intros s t n i seg cnt10 cnt11 cnt20 cnt21 block
    Hslen Hi Hseg Hcnt Hscratch Hblock Hbit.
  subst block.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  unfold EditCountBounds in *.
  destruct H21 as [H21_len H21_bound].
  split; [exact H10|].
  split; [exact H11|].
  split; [exact H20|].
  split.
  - rewrite Zlength_replace_Znth. exact H21_len.
  - intros idx Hidx.
    assert (0 <= Znth i seg 0 < n) as Hsegblock_bound.
    {
      pose proof Hseg as Hseg_tmp.
      unfold EditSegmentPrefix in Hseg_tmp.
      destruct Hseg_tmp as [_ Hseg_prop].
      pose proof (Hseg_prop i ltac:(lia)) as Hstart_i.
      unfold EditBlockStart in Hstart_i.
      destruct Hstart_i as [[Hlo Hhi] _].
      lia.
    }
    destruct (Z.eq_dec idx (Znth i seg 0)) as [Heq | Hneq].
    + subst idx.
      rewrite Znth_replace_Znth_Same by (rewrite H21_len; exact Hidx).
      assert (edit_block_startb t i (Znth i seg 0) = true) as Hstart_bool.
      {
        unfold EditSegmentPrefix in Hseg.
        destruct Hseg as [_ Hseg_prop].
        apply (proj2 (edit_block_startb_true_iff__build_s2_segments_counts
          t i (Znth i seg 0))).
        apply Hseg_prop.
        lia.
      }
      unfold EditCountsForPrefix in Hcnt.
      destruct Hcnt as [_ [_ [_ Hcnt1]]].
      rewrite Hcnt1 by exact Hidx.
      replace (edit_count_bit_in_block_prefix s t i (Znth i seg 0) 1 + 1)
        with (edit_count_bit_in_block_prefix s t (i + 1) (Znth i seg 0) 1).
      2:{
        rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
          with (n := n); auto.
        rewrite Hstart_bool.
        unfold edit_bit_atb.
        rewrite Hbit.
        simpl.
        lia.
      }
      apply edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts;
        lia || exact Hslen.
    + rewrite Znth_replace_Znth_Diff
        by (try rewrite H21_len; try exact Hidx; try exact Hsegblock_bound; lia).
      apply H21_bound.
      exact Hidx.
Qed.
Lemma edit_scratch_bound_update_zero__build_s2_segments_counts :
  forall s t n i seg cnt10 cnt11 cnt20 cnt21 block,
    Zlength s = n ->
    0 <= i < n ->
    EditSegmentPrefix t (i + 1) seg ->
    EditCountsForPrefix s t n i cnt20 cnt21 ->
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 ->
    block = Znth i seg 0 ->
    Znth i s 0 = 0 ->
    EditScratchCountsBound n cnt10 cnt11
      (replace_Znth block (Znth block cnt20 0 + 1) cnt20) cnt21.
Proof.
  intros s t n i seg cnt10 cnt11 cnt20 cnt21 block
    Hslen Hi Hseg Hcnt Hscratch Hblock Hbit.
  subst block.
  unfold EditScratchCountsBound in *.
  destruct Hscratch as [H10 [H11 [H20 H21]]].
  unfold EditCountBounds in *.
  destruct H20 as [H20_len H20_bound].
  split; [exact H10|].
  split; [exact H11|].
  split.
  - split.
    + rewrite Zlength_replace_Znth. exact H20_len.
    + intros idx Hidx.
      assert (0 <= Znth i seg 0 < n) as Hsegblock_bound.
      {
        pose proof Hseg as Hseg_tmp.
        unfold EditSegmentPrefix in Hseg_tmp.
        destruct Hseg_tmp as [_ Hseg_prop].
        pose proof (Hseg_prop i ltac:(lia)) as Hstart_i.
        unfold EditBlockStart in Hstart_i.
        destruct Hstart_i as [[Hlo Hhi] _].
        lia.
      }
      destruct (Z.eq_dec idx (Znth i seg 0)) as [Heq | Hneq].
      * subst idx.
        rewrite Znth_replace_Znth_Same by (rewrite H20_len; exact Hidx).
        assert (edit_block_startb t i (Znth i seg 0) = true) as Hstart_bool.
        {
          unfold EditSegmentPrefix in Hseg.
          destruct Hseg as [_ Hseg_prop].
          apply (proj2 (edit_block_startb_true_iff__build_s2_segments_counts
            t i (Znth i seg 0))).
          apply Hseg_prop.
          lia.
        }
        unfold EditCountsForPrefix in Hcnt.
        destruct Hcnt as [_ [_ [Hcnt0 _]]].
        rewrite Hcnt0 by exact Hidx.
        replace (edit_count_bit_in_block_prefix s t i (Znth i seg 0) 0 + 1)
          with (edit_count_bit_in_block_prefix s t (i + 1) (Znth i seg 0) 0).
        2:{
          rewrite edit_count_bit_in_block_prefix_succ__build_s2_segments_counts
            with (n := n); auto.
          rewrite Hstart_bool.
          unfold edit_bit_atb.
          rewrite Hbit.
          simpl.
          lia.
        }
        apply edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts;
          lia || exact Hslen.
      * rewrite Znth_replace_Znth_Diff
          by (try rewrite H20_len; try exact Hidx; try exact Hsegblock_bound; lia).
        apply H20_bound.
        exact Hidx.
  - exact H21.
Qed.
Lemma edit_NoDup_map_inj__greedy_common_and_mismatch_steps :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  induction Hnd as [|x l Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hy]].
      assert (x = y).
      { apply Hinj; simpl; auto. }
      subst y. contradiction.
    + apply IH.
      intros a b Ha Hb Hab.
      apply Hinj; simpl; auto.
Qed.
Lemma edit_zrange_nodup__greedy_common_and_mismatch_steps :
  forall n, NoDup (edit_zrange n).
Proof.
  intro n.
  unfold edit_zrange.
  apply edit_NoDup_map_inj__greedy_common_and_mismatch_steps.
  - intros x y _ _ Hxy.
    lia.
  - apply seq_NoDup.
Qed.
Lemma edit_zrange_in__greedy_common_and_mismatch_steps :
  forall n idx,
    0 <= idx < n ->
    In idx (edit_zrange n).
Proof.
  intros n idx Hidx.
  unfold edit_zrange.
  apply in_map_iff.
  exists (Z.to_nat idx).
  split.
  - rewrite Z2Nat.id; lia.
  - apply in_seq.
    split; [lia|].
    apply Z2Nat.inj_lt; lia.
Qed.
Lemma edit_zrange_in_bounds__greedy_common_and_mismatch_steps :
  forall n idx,
    In idx (edit_zrange n) ->
    0 <= idx < n.
Proof.
  intros n idx Hin.
  unfold edit_zrange in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [off [Hidx Hoff]].
  subst idx.
  apply in_seq in Hoff.
  destruct Hoff as [_ Hoff].
  split; [lia|].
  destruct (Z_le_dec 0 n) as [Hnonneg | Hneg].
  - assert (Z.of_nat off < n).
    {
      rewrite <- (Z2Nat.id n) by lia.
      apply Nat2Z.inj_lt.
      exact Hoff.
    }
    lia.
  - replace (Z.to_nat n) with O in Hoff
      by (destruct n; try lia; reflexivity).
    lia.
Qed.
Lemma edit_edge_openb_true_iff__greedy_common_and_mismatch_steps :
  forall t idx,
    edit_edge_openb t idx = true <-> edit_edge_open t idx.
Proof.
  intros t idx.
  unfold edit_edge_openb, edit_edge_open.
  rewrite andb_true_iff.
  repeat rewrite Z.eqb_eq.
  tauto.
Qed.
Lemma edit_all_edges_openb_true__greedy_common_and_mismatch_steps :
  forall t lo hi,
    (forall k, lo <= k < hi -> edit_edge_open t k) ->
    edit_all_edges_openb t lo hi = true.
Proof.
  intros t lo hi Hedges.
  unfold edit_all_edges_openb.
  apply forallb_forall.
  intros x Hin.
  apply edit_edge_openb_true_iff__greedy_common_and_mismatch_steps.
  apply Hedges.
  unfold edit_zrange_between in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [off [Hx Hoff]].
  subst x.
  apply in_seq in Hoff.
  destruct Hoff as [_ Hoff].
  split; [lia|].
  destruct (Z_le_dec 0 (hi - lo)) as [Hnonneg | Hneg].
  - assert (Z.of_nat off < hi - lo).
    {
      rewrite <- (Z2Nat.id (hi - lo)) by lia.
      apply Nat2Z.inj_lt.
      exact Hoff.
    }
    lia.
  - replace (Z.to_nat (hi - lo)) with O in Hoff
      by (destruct (hi - lo); try lia; reflexivity).
    lia.
Qed.
Lemma edit_block_startb_true__greedy_common_and_mismatch_steps :
  forall t idx start,
    EditBlockStart t idx start ->
    edit_block_startb t idx start = true.
Proof.
  intros t idx start Hstart.
  unfold EditBlockStart in Hstart.
  destruct Hstart as [Hrange [Hedges Hstart_edge]].
  unfold edit_block_startb.
  apply andb_true_intro.
  split.
  - apply andb_true_intro.
    split.
    + apply andb_true_intro.
      split; apply Z.leb_le; lia.
    + apply edit_all_edges_openb_true__greedy_common_and_mismatch_steps.
      intros k Hk.
      apply Hedges; lia.
  - destruct Hstart_edge as [Hzero | Hnot_edge].
    + subst start. simpl. reflexivity.
    + apply orb_true_intro.
      right.
      destruct (edit_edge_openb t start) eqn:Hedge; [|reflexivity].
      apply edit_edge_openb_true_iff__greedy_common_and_mismatch_steps in Hedge.
      contradiction.
Qed.
Lemma edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps :
  forall s t n seg full0 full1 i,
    EditBuildState s t n n seg full0 full1 ->
    0 <= i < n ->
    edit_count_positions_in_seg_prefix seg i (Znth i seg 0) <
      Znth (Znth i seg 0) full0 0 + Znth (Znth i seg 0) full1 0.
Proof.
  intros s t n seg full0 full1 i Hbuild Hi.
  pose proof Hbuild as Hbuild_copy.
  unfold EditBuildState in Hbuild_copy.
  destruct Hbuild_copy as [_ [Hbin [_ [Hseg Hcounts]]]].
  destruct Hbin as [Hs_len Hbin].
  destruct Hseg as [Hseg_len Hseg].
  destruct Hcounts as [Hfull0_len [Hfull1_len [Hcnt0 Hcnt1]]].
  set (block := Znth i seg 0).
  assert (Hblock_range : 0 <= block < n).
  {
    subst block.
    specialize (Hseg i Hi).
    unfold EditBlockStart in Hseg.
    lia.
  }
  specialize (Hcnt0 block Hblock_range).
  specialize (Hcnt1 block Hblock_range).
  rewrite Hcnt0, Hcnt1.
  unfold edit_count_positions_in_seg_prefix, edit_count_bit_in_block_prefix.
  rewrite Hseg_len, Hs_len.
  set (range := edit_zrange n).
  set (P := fun idx : Z =>
    (idx <? i) && Z.eqb (Znth idx seg 0) block).
  set (Q0 := fun idx : Z =>
    (idx <? n) && edit_block_startb t idx block && edit_bit_atb s idx 0).
  set (Q1 := fun idx : Z =>
    (idx <? n) && edit_block_startb t idx block && edit_bit_atb s idx 1).
  change (Z.of_nat (length (filter P range)) <
    Z.of_nat (length (filter Q0 range)) +
    Z.of_nat (length (filter Q1 range))).
  assert (Hin_i_range : In i range).
  {
    subst range. apply edit_zrange_in__greedy_common_and_mismatch_steps. exact Hi.
  }
  assert (Hi_not_pref : ~ In i (filter P range)).
  {
    intro Hin.
    apply filter_In in Hin.
    destruct Hin as [_ HP].
    subst P.
    apply andb_true_iff in HP.
    destruct HP as [Hlt _].
    apply Z.ltb_lt in Hlt.
    lia.
  }
  assert (Hnodup_source : NoDup (i :: filter P range)).
  {
    constructor.
    - exact Hi_not_pref.
    - apply NoDup_filter.
      subst range. apply edit_zrange_nodup__greedy_common_and_mismatch_steps.
  }
  assert (Hincl : incl (i :: filter P range) (filter Q0 range ++ filter Q1 range)).
  {
    intros x Hx.
    simpl in Hx.
    apply in_app_iff.
    destruct Hx as [Hx | Hx].
    - subst x.
      specialize (Hseg i Hi).
      pose proof Hseg as Hstart.
      destruct (Hbin i Hi) as [Hbit | Hbit].
      + left.
        apply filter_In.
        split; [exact Hin_i_range|].
        subst Q0.
        apply andb_true_intro.
        split.
        * apply andb_true_intro.
          split; [apply Z.ltb_lt; lia|].
          subst block. apply edit_block_startb_true__greedy_common_and_mismatch_steps. exact Hstart.
        * unfold edit_bit_atb. rewrite Hbit. apply Z.eqb_refl.
      + right.
        apply filter_In.
        split; [exact Hin_i_range|].
        subst Q1.
        apply andb_true_intro.
        split.
        * apply andb_true_intro.
          split; [apply Z.ltb_lt; lia|].
          subst block. apply edit_block_startb_true__greedy_common_and_mismatch_steps. exact Hstart.
        * unfold edit_bit_atb. rewrite Hbit. apply Z.eqb_refl.
    - apply filter_In in Hx.
      destruct Hx as [Hx_range HP].
      subst P.
      apply andb_true_iff in HP.
      destruct HP as [Hlt Hblock].
      apply Z.ltb_lt in Hlt.
      apply Z.eqb_eq in Hblock.
      pose proof (edit_zrange_in_bounds__greedy_common_and_mismatch_steps n x ltac:(subst range; exact Hx_range))
        as Hx_bounds.
      specialize (Hseg x Hx_bounds).
      rewrite Hblock in Hseg.
      destruct (Hbin x Hx_bounds) as [Hbit | Hbit].
      + left.
        apply filter_In.
        split; [exact Hx_range|].
        subst Q0.
        apply andb_true_intro.
        split.
        * apply andb_true_intro.
          split; [apply Z.ltb_lt; lia|].
          apply edit_block_startb_true__greedy_common_and_mismatch_steps. exact Hseg.
        * unfold edit_bit_atb. rewrite Hbit. apply Z.eqb_refl.
      + right.
        apply filter_In.
        split; [exact Hx_range|].
        subst Q1.
        apply andb_true_intro.
        split.
        * apply andb_true_intro.
          split; [apply Z.ltb_lt; lia|].
          apply edit_block_startb_true__greedy_common_and_mismatch_steps. exact Hseg.
        * unfold edit_bit_atb. rewrite Hbit. apply Z.eqb_refl.
  }
  pose proof (@NoDup_incl_length Z
    (i :: filter P range)
    (filter Q0 range ++ filter Q1 range)
    Hnodup_source Hincl) as Hle.
  simpl in Hle.
  rewrite length_app in Hle.
  lia.
Qed.
Lemma edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyCurrentAvailability n i seg1 seg2 cnt10 cnt11 cnt20 cnt21.
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hi.
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [_ [_ [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch [Hremaining Hcons]]]]]]]]]].
  unfold EditGreedyRemainingTotals in Hremaining.
  destruct Hremaining as [Hrem1 Hrem2].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [[Hlen1 Hseg1] Hcounts1]]]].
  destruct Hbuild2_copy as [_ [_ [_ [[Hlen2 Hseg2] Hcounts2]]]].
  specialize (Hseg1 i Hi).
  specialize (Hseg2 i Hi).
  unfold EditBlockStart in Hseg1, Hseg2.
  destruct Hseg1 as [Hseg1_range _].
  destruct Hseg2 as [Hseg2_range _].
  assert (Hseg1_idx : 0 <= Znth i seg1 0 < n) by lia.
  assert (Hseg2_idx : 0 <= Znth i seg2 0 < n) by lia.
  pose proof (edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps
    s1 t1 n seg1 full10 full11 i Hbuild1 Hi) as Hlt1.
  pose proof (edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps
    s2 t2 n seg2 full20 full21 i Hbuild2 Hi) as Hlt2.
  repeat split; try lia.
  - rewrite Hrem1 by (rewrite Hlen1; exact Hseg1_idx).
    lia.
  - rewrite Hrem2 by (rewrite Hlen2; exact Hseg2_idx).
    lia.
Qed.
Lemma edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps :
  forall seg block,
    edit_count_positions_in_seg_prefix seg 0 block = 0.
Proof.
  intros seg block.
  unfold edit_count_positions_in_seg_prefix.
  destruct (filter
    (fun idx : Z => (idx <? 0) && (Znth idx seg 0 =? block))
    (edit_zrange (Zlength seg))) as [|x xs] eqn:Hfilter.
  - reflexivity.
  - exfalso.
    assert (Hin_filter : In x (x :: xs)) by (left; reflexivity).
    rewrite <- Hfilter in Hin_filter.
    apply filter_In in Hin_filter.
    destruct Hin_filter as [Hin_range Hpred].
    apply andb_true_iff in Hpred.
    destruct Hpred as [Hlt _].
    apply Z.ltb_lt in Hlt.
    pose proof (edit_zrange_in_bounds__greedy_common_and_mismatch_steps (Zlength seg) x Hin_range).
    lia.
Qed.
Lemma edit_count_positions_step_same__greedy_common_and_mismatch_steps :
  forall seg i block,
    0 <= i < Zlength seg ->
    block = Znth i seg 0 ->
    edit_count_positions_in_seg_prefix seg (i + 1) block =
    edit_count_positions_in_seg_prefix seg i block + 1.
Proof.
  intros seg i block Hi Hblock.
  subst block.
  unfold edit_count_positions_in_seg_prefix.
  set (range := edit_zrange (Zlength seg)).
  set (P := fun idx : Z =>
    (idx <? i) && (Znth idx seg 0 =? Znth i seg 0)).
  set (Pnext := fun idx : Z =>
    (idx <? i + 1) && (Znth idx seg 0 =? Znth i seg 0)).
  change (Z.of_nat (length (filter Pnext range)) =
    Z.of_nat (length (filter P range)) + 1).
  assert (Hin_i_range : In i range).
  {
    subst range. apply edit_zrange_in__greedy_common_and_mismatch_steps. exact Hi.
  }
  assert (Hi_not_pref : ~ In i (filter P range)).
  {
    intro Hin.
    apply filter_In in Hin.
    destruct Hin as [_ HP].
    subst P.
    apply andb_true_iff in HP.
    destruct HP as [Hlt _].
    apply Z.ltb_lt in Hlt.
    lia.
  }
  assert (Hnodup_source : NoDup (i :: filter P range)).
  {
    constructor.
    - exact Hi_not_pref.
    - apply NoDup_filter.
      subst range. apply edit_zrange_nodup__greedy_common_and_mismatch_steps.
  }
  assert (Hnodup_target : NoDup (filter Pnext range)).
  {
    apply NoDup_filter.
    subst range. apply edit_zrange_nodup__greedy_common_and_mismatch_steps.
  }
  assert (Hincl_source_target : incl (i :: filter P range) (filter Pnext range)).
  {
    intros x Hx.
    simpl in Hx.
    apply filter_In.
    destruct Hx as [Hx | Hx].
    - subst x.
      split; [exact Hin_i_range|].
      subst Pnext.
      apply andb_true_intro.
      split; [apply Z.ltb_lt; lia|apply Z.eqb_refl].
    - apply filter_In in Hx.
      destruct Hx as [Hx_range HP].
      split; [exact Hx_range|].
      subst P Pnext.
      apply andb_true_iff in HP.
      destruct HP as [Hlt Heq].
      apply Z.ltb_lt in Hlt.
      apply andb_true_intro.
      split; [apply Z.ltb_lt; lia|exact Heq].
  }
  assert (Hincl_target_source : incl (filter Pnext range) (i :: filter P range)).
  {
    intros x Hx.
    apply filter_In in Hx.
    destruct Hx as [Hx_range HP].
    subst Pnext.
    apply andb_true_iff in HP.
    destruct HP as [Hlt Heq].
    apply Z.ltb_lt in Hlt.
    simpl.
    destruct (Z.eq_dec x i) as [Heq_x | Hneq_x].
    - left. symmetry. exact Heq_x.
    - right.
      apply filter_In.
      split; [exact Hx_range|].
      subst P.
      apply andb_true_intro.
      split; [apply Z.ltb_lt; lia|exact Heq].
  }
  pose proof (@NoDup_incl_length Z
    (i :: filter P range) (filter Pnext range)
    Hnodup_source Hincl_source_target) as Hle1.
  pose proof (@NoDup_incl_length Z
    (filter Pnext range) (i :: filter P range)
    Hnodup_target Hincl_target_source) as Hle2.
  assert (Hlen_eq : length (filter Pnext range) = length (i :: filter P range))
    by lia.
  rewrite Hlen_eq.
  simpl.
  lia.
Qed.
Lemma edit_count_positions_step_diff__greedy_common_and_mismatch_steps :
  forall seg i block,
    0 <= i < Zlength seg ->
    Znth i seg 0 <> block ->
    edit_count_positions_in_seg_prefix seg (i + 1) block =
    edit_count_positions_in_seg_prefix seg i block.
Proof.
  intros seg i block Hi Hdiff.
  unfold edit_count_positions_in_seg_prefix.
  set (range := edit_zrange (Zlength seg)).
  set (P := fun idx : Z =>
    (idx <? i) && (Znth idx seg 0 =? block)).
  set (Pnext := fun idx : Z =>
    (idx <? i + 1) && (Znth idx seg 0 =? block)).
  change (Z.of_nat (length (filter Pnext range)) =
    Z.of_nat (length (filter P range))).
  assert (Hnodup_P : NoDup (filter P range)).
  {
    apply NoDup_filter.
    subst range. apply edit_zrange_nodup__greedy_common_and_mismatch_steps.
  }
  assert (Hnodup_Pnext : NoDup (filter Pnext range)).
  {
    apply NoDup_filter.
    subst range. apply edit_zrange_nodup__greedy_common_and_mismatch_steps.
  }
  assert (Hincl_P_Pnext : incl (filter P range) (filter Pnext range)).
  {
    intros x Hx.
    apply filter_In in Hx.
    destruct Hx as [Hx_range HP].
    apply filter_In.
    split; [exact Hx_range|].
    subst P Pnext.
    apply andb_true_iff in HP.
    destruct HP as [Hlt Heq].
    apply Z.ltb_lt in Hlt.
    apply andb_true_intro.
    split; [apply Z.ltb_lt; lia|exact Heq].
  }
  assert (Hincl_Pnext_P : incl (filter Pnext range) (filter P range)).
  {
    intros x Hx.
    apply filter_In in Hx.
    destruct Hx as [Hx_range HP].
    subst Pnext.
    apply andb_true_iff in HP.
    destruct HP as [Hlt Heq].
    apply Z.ltb_lt in Hlt.
    destruct (Z.eq_dec x i) as [Heq_x | Hneq_x].
    - subst x.
      apply Z.eqb_eq in Heq.
      contradiction.
    - apply filter_In.
      split; [exact Hx_range|].
      subst P.
      apply andb_true_intro.
      split; [apply Z.ltb_lt; lia|exact Heq].
  }
  pose proof (@NoDup_incl_length Z
    (filter P range) (filter Pnext range)
    Hnodup_P Hincl_P_Pnext) as Hle1.
  pose proof (@NoDup_incl_length Z
    (filter Pnext range) (filter P range)
    Hnodup_Pnext Hincl_Pnext_P) as Hle2.
  assert (Hlen_eq : length (filter Pnext range) = length (filter P range))
    by lia.
  rewrite Hlen_eq.
  reflexivity.
Qed.
Lemma edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps :
  forall seg i full0 full1 cnt0 cnt1 idx,
    0 <= i < Zlength seg ->
    idx = Znth i seg 0 ->
    0 <= idx < Zlength seg ->
    Zlength cnt0 = Zlength seg ->
    (forall block,
        0 <= block < Zlength seg ->
        Znth block cnt0 0 + Znth block cnt1 0 =
        Znth block full0 0 + Znth block full1 0 -
        edit_count_positions_in_seg_prefix seg i block) ->
    forall block,
      0 <= block < Zlength seg ->
      Znth block (replace_Znth idx (Znth idx cnt0 0 - 1) cnt0) 0 +
        Znth block cnt1 0 =
      Znth block full0 0 + Znth block full1 0 -
        edit_count_positions_in_seg_prefix seg (i + 1) block.
Proof.
  intros seg i full0 full1 cnt0 cnt1 idx Hi Hidx Hidx_range Hcnt0_len Hrem block Hblock.
  subst idx.
  destruct (Z.eq_dec (Znth i seg 0) block) as [Heq | Hneq].
  - subst block.
    rewrite Znth_replace_Znth_Same by (rewrite Hcnt0_len; lia).
    pose proof (Hrem (Znth i seg 0) ltac:(lia)) as Hold.
    rewrite edit_count_positions_step_same__greedy_common_and_mismatch_steps by (lia || reflexivity).
    lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hcnt0_len; try lia; exact Hneq).
    rewrite Hrem by lia.
    rewrite edit_count_positions_step_diff__greedy_common_and_mismatch_steps by (lia || exact Hneq).
    lia.
Qed.
Lemma edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps :
  forall seg i full0 full1 cnt0 cnt1 idx,
    0 <= i < Zlength seg ->
    idx = Znth i seg 0 ->
    0 <= idx < Zlength seg ->
    Zlength cnt1 = Zlength seg ->
    (forall block,
        0 <= block < Zlength seg ->
        Znth block cnt0 0 + Znth block cnt1 0 =
        Znth block full0 0 + Znth block full1 0 -
        edit_count_positions_in_seg_prefix seg i block) ->
    forall block,
      0 <= block < Zlength seg ->
      Znth block cnt0 0 +
        Znth block (replace_Znth idx (Znth idx cnt1 0 - 1) cnt1) 0 =
      Znth block full0 0 + Znth block full1 0 -
        edit_count_positions_in_seg_prefix seg (i + 1) block.
Proof.
  intros seg i full0 full1 cnt0 cnt1 idx Hi Hidx Hidx_range Hcnt1_len Hrem block Hblock.
  subst idx.
  destruct (Z.eq_dec (Znth i seg 0) block) as [Heq | Hneq].
  - subst block.
    rewrite Znth_replace_Znth_Same by (rewrite Hcnt1_len; lia).
    pose proof (Hrem (Znth i seg 0) ltac:(lia)) as Hold.
    rewrite edit_count_positions_step_same__greedy_common_and_mismatch_steps by (lia || reflexivity).
    lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hcnt1_len; try lia; exact Hneq).
    rewrite Hrem by lia.
    rewrite edit_count_positions_step_diff__greedy_common_and_mismatch_steps by (lia || exact Hneq).
    lia.
Qed.
Lemma edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps :
  forall n cnt idx,
    EditCountBounds n cnt ->
    0 <= idx < n ->
    0 < Znth idx cnt 0 ->
    EditCountBounds n (replace_Znth idx (Znth idx cnt 0 - 1) cnt).
Proof.
  intros n cnt idx [Hlen Hbounds] Hidx Hpos.
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros j Hj.
    pose proof (Hbounds idx Hidx) as Hidx_bounds.
    destruct (Z.eq_dec j idx) as [Heq | Hneq].
    + subst j.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
      apply Hbounds. lia.
Qed.
Lemma edit_greedy_prefix_state_start__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditBuildState s1 t1 n n seg1 cnt10 cnt11 ->
    EditBuildState s2 t2 n n seg2 cnt20 cnt21 ->
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 ->
    EditGreedyPrefixState s1 s2 t1 t2 n 0 0
      seg1 seg2 cnt10 cnt11 cnt20 cnt21.
Proof.
  intros s1 s2 t1 t2 n seg1 seg2 cnt10 cnt11 cnt20 cnt21
    Hbuild1 Hbuild2 Hscratch.
  unfold EditGreedyPrefixState.
  pose proof Hbuild1 as Hbuild1_copy.
  destruct Hbuild1_copy as [Hrange _].
  split; [lia|].
  split; [lia|].
  exists cnt10, cnt11, cnt20, cnt21.
  split; [exact Hbuild1|].
  split; [exact Hbuild2|].
  split; [exact Hscratch|].
  split.
  - unfold EditGreedyRemainingTotals.
    split; intros block Hblock;
      rewrite edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps; lia.
  - constructor.
Qed.
Lemma edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    0 <= i < n ->
    0 <= Znth i seg1 0 < n /\
    0 <= Znth i seg2 0 < n /\
    0 <= Znth (Znth i seg1 0) cnt10 0 <= n /\
    0 <= Znth (Znth i seg1 0) cnt11 0 <= n /\
    0 <= Znth (Znth i seg2 0) cnt20 0 <= n /\
    0 <= Znth (Znth i seg2 0) cnt21 0 <= n.
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21
    Hstate Hi.
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [_ [_ [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch _]]]]]]]]].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [Hseg1 _]]]].
  destruct Hbuild2_copy as [_ [_ [_ [Hseg2 _]]]].
  destruct Hseg1 as [_ Hseg1].
  destruct Hseg2 as [_ Hseg2].
  specialize (Hseg1 i Hi).
  specialize (Hseg2 i Hi).
  unfold EditBlockStart in Hseg1, Hseg2.
  destruct Hseg1 as [Hseg1_range _].
  destruct Hseg2 as [Hseg2_range _].
  assert (Hseg1_idx : 0 <= Znth i seg1 0 < n) by lia.
  assert (Hseg2_idx : 0 <= Znth i seg2 0 < n) by lia.
  unfold EditScratchCountsBound in Hscratch.
  destruct Hscratch as [[_ Hcnt10] [[_ Hcnt11] [[_ Hcnt20] [_ Hcnt21]]]].
  pose proof (Hcnt10 (Znth i seg1 0) Hseg1_idx) as Hc10.
  pose proof (Hcnt11 (Znth i seg1 0) Hseg1_idx) as Hc11.
  pose proof (Hcnt20 (Znth i seg2 0) Hseg2_idx) as Hc20.
  pose proof (Hcnt21 (Znth i seg2 0) Hseg2_idx) as Hc21.
  repeat split; lia.
Qed.
Lemma edit_greedy_common_zero_step__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    0 <= i < n ->
    a = Znth i seg1 0 ->
    b = Znth i seg2 0 ->
    0 < Znth a cnt10 0 ->
    0 < Znth b cnt20 0 ->
    EditGreedyPrefixState s1 s2 t1 t2 n (i + 1) (ans + 1)
      seg1 seg2
      (replace_Znth a (Znth a cnt10 0 - 1) cnt10)
      cnt11
      (replace_Znth b (Znth b cnt20 0 - 1) cnt20)
      cnt21.
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b
    Hstate Hi Ha Hb Hpos10 Hpos20.
  pose proof (edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hi)
    as [Hseg1_range [Hseg2_range _]].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [Hirange [Hans [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch [Hremaining Hcons]]]]]]]]]].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [[Hlen1 _] _]]]].
  destruct Hbuild2_copy as [_ [_ [_ [[Hlen2 _] _]]]].
  pose proof Hscratch as Hscratch_lengths.
  unfold EditScratchCountsBound in Hscratch_lengths.
  destruct Hscratch_lengths as [[Hcnt10_len _] [[Hcnt11_len _] [[Hcnt20_len _] [Hcnt21_len _]]]].
  subst a b.
  unfold EditGreedyPrefixState.
  split; [lia|].
  split; [lia|].
  exists full10, full11, full20, full21.
  split; [exact Hbuild1|].
  split; [exact Hbuild2|].
  split.
  - unfold EditScratchCountsBound in *.
    destruct Hscratch as [Hcnt10 [Hcnt11 [Hcnt20 Hcnt21]]].
    refine (conj _ (conj _ (conj _ _))).
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + exact Hcnt11.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + exact Hcnt21.
  - split.
    + unfold EditGreedyRemainingTotals in *.
      destruct Hremaining as [Hrem1 Hrem2].
      split.
      * eapply edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps; eauto; lia.
      * eapply edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps; eauto; lia.
    + eapply EditGreedyConsumedPrefix_common_zero; eauto; lia.
Qed.
Lemma edit_greedy_common_one_step__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    0 <= i < n ->
    a = Znth i seg1 0 ->
    b = Znth i seg2 0 ->
    ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
    0 < Znth a cnt11 0 ->
    0 < Znth b cnt21 0 ->
    EditGreedyPrefixState s1 s2 t1 t2 n (i + 1) (ans + 1)
      seg1 seg2
      cnt10
      (replace_Znth a (Znth a cnt11 0 - 1) cnt11)
      cnt20
      (replace_Znth b (Znth b cnt21 0 - 1) cnt21).
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b
    Hstate Hi Ha Hb Hnot_common_zero Hpos11 Hpos21.
  pose proof (edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hi)
    as [Hseg1_range [Hseg2_range _]].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [Hirange [Hans [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch [Hremaining Hcons]]]]]]]]]].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [[Hlen1 _] _]]]].
  destruct Hbuild2_copy as [_ [_ [_ [[Hlen2 _] _]]]].
  pose proof Hscratch as Hscratch_lengths.
  unfold EditScratchCountsBound in Hscratch_lengths.
  destruct Hscratch_lengths as [[Hcnt10_len _] [[Hcnt11_len _] [[Hcnt20_len _] [Hcnt21_len _]]]].
  subst a b.
  unfold EditGreedyPrefixState.
  split; [lia|].
  split; [lia|].
  exists full10, full11, full20, full21.
  split; [exact Hbuild1|].
  split; [exact Hbuild2|].
  split.
  - unfold EditScratchCountsBound in *.
    destruct Hscratch as [Hcnt10 [Hcnt11 [Hcnt20 Hcnt21]]].
    refine (conj _ (conj _ (conj _ _))).
    + exact Hcnt10.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + exact Hcnt20.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
  - split.
    + unfold EditGreedyRemainingTotals in *.
      destruct Hremaining as [Hrem1 Hrem2].
      split.
      * eapply edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps; eauto; lia.
      * eapply edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps; eauto; lia.
    + eapply EditGreedyConsumedPrefix_common_one; eauto; lia.
Qed.
Lemma edit_greedy_s1_zero_s2_one_step__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    0 <= i < n ->
    a = Znth i seg1 0 ->
    b = Znth i seg2 0 ->
    ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
    ~ (0 < Znth a cnt11 0 /\ 0 < Znth b cnt21 0) ->
    0 < Znth a cnt10 0 ->
    0 < Znth b cnt21 0 ->
    EditGreedyPrefixState s1 s2 t1 t2 n (i + 1) ans
      seg1 seg2
      (replace_Znth a (Znth a cnt10 0 - 1) cnt10)
      cnt11
      cnt20
      (replace_Znth b (Znth b cnt21 0 - 1) cnt21).
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b
    Hstate Hi Ha Hb Hnot_common_zero Hnot_common_one Hpos10 Hpos21.
  pose proof (edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hi)
    as [Hseg1_range [Hseg2_range _]].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [Hirange [Hans [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch [Hremaining Hcons]]]]]]]]]].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [[Hlen1 _] _]]]].
  destruct Hbuild2_copy as [_ [_ [_ [[Hlen2 _] _]]]].
  pose proof Hscratch as Hscratch_lengths.
  unfold EditScratchCountsBound in Hscratch_lengths.
  destruct Hscratch_lengths as [[Hcnt10_len _] [[Hcnt11_len _] [[Hcnt20_len _] [Hcnt21_len _]]]].
  subst a b.
  unfold EditGreedyPrefixState.
  split; [lia|].
  split; [lia|].
  exists full10, full11, full20, full21.
  split; [exact Hbuild1|].
  split; [exact Hbuild2|].
  split.
  - unfold EditScratchCountsBound in *.
    destruct Hscratch as [Hcnt10 [Hcnt11 [Hcnt20 Hcnt21]]].
    refine (conj _ (conj _ (conj _ _))).
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + exact Hcnt11.
    + exact Hcnt20.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
  - split.
    + unfold EditGreedyRemainingTotals in *.
      destruct Hremaining as [Hrem1 Hrem2].
      split.
      * eapply edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps; eauto; lia.
      * eapply edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps; eauto; lia.
    + eapply EditGreedyConsumedPrefix_s1_zero_s2_one; eauto; lia.
Qed.
Lemma edit_greedy_s1_one_s2_zero_step__greedy_common_and_mismatch_steps :
  forall s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b,
    EditGreedyPrefixState s1 s2 t1 t2 n i ans
      seg1 seg2 cnt10 cnt11 cnt20 cnt21 ->
    0 <= i < n ->
    a = Znth i seg1 0 ->
    b = Znth i seg2 0 ->
    ~ (0 < Znth a cnt10 0 /\ 0 < Znth b cnt20 0) ->
    ~ (0 < Znth a cnt11 0 /\ 0 < Znth b cnt21 0) ->
    ~ (0 < Znth a cnt10 0) ->
    0 < Znth a cnt11 0 ->
    0 < Znth b cnt20 0 ->
    EditGreedyPrefixState s1 s2 t1 t2 n (i + 1) ans
      seg1 seg2
      cnt10
      (replace_Znth a (Znth a cnt11 0 - 1) cnt11)
      (replace_Znth b (Znth b cnt20 0 - 1) cnt20)
      cnt21.
Proof.
  intros s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 a b
    Hstate Hi Ha Hb Hnot_common_zero Hnot_common_one Hnot10 Hpos11 Hpos20.
  pose proof (edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 Hstate Hi)
    as [Hseg1_range [Hseg2_range _]].
  unfold EditGreedyPrefixState in Hstate.
  destruct Hstate as [Hirange [Hans [full10 [full11 [full20 [full21
    [Hbuild1 [Hbuild2 [Hscratch [Hremaining Hcons]]]]]]]]]].
  pose proof Hbuild1 as Hbuild1_copy.
  pose proof Hbuild2 as Hbuild2_copy.
  destruct Hbuild1_copy as [_ [_ [_ [[Hlen1 _] _]]]].
  destruct Hbuild2_copy as [_ [_ [_ [[Hlen2 _] _]]]].
  pose proof Hscratch as Hscratch_lengths.
  unfold EditScratchCountsBound in Hscratch_lengths.
  destruct Hscratch_lengths as [[Hcnt10_len _] [[Hcnt11_len _] [[Hcnt20_len _] [Hcnt21_len _]]]].
  subst a b.
  unfold EditGreedyPrefixState.
  split; [lia|].
  split; [lia|].
  exists full10, full11, full20, full21.
  split; [exact Hbuild1|].
  split; [exact Hbuild2|].
  split.
  - unfold EditScratchCountsBound in *.
    destruct Hscratch as [Hcnt10 [Hcnt11 [Hcnt20 Hcnt21]]].
    refine (conj _ (conj _ (conj _ _))).
    + exact Hcnt10.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + eapply edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps; eauto.
    + exact Hcnt21.
  - split.
    + unfold EditGreedyRemainingTotals in *.
      destruct Hremaining as [Hrem1 Hrem2].
      split.
      * eapply edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps; eauto; lia.
      * eapply edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps; eauto; lia.
    + eapply EditGreedyConsumedPrefix_s1_one_s2_zero; eauto; lia.
Qed.

From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
Require Import Coq.Relations.Relation_Operators.

(** Legacy region/count interfaces retained for the existing helper proofs.
    The public C contract below uses EditStringsAnswer and legal swaps. *)
Definition EditOpenEdgesTest (t : list Z) (lo hi : Z) : bool :=
  forallb (edit_edge_openb t) (Zrange lo hi).
Definition EditBlockStartTest (t : list Z) (idx start : Z) : bool :=
  Z.leb 0 start && Z.leb start idx &&
  EditOpenEdgesTest t (start + 1) (idx + 1) &&
  (Z.eqb start 0 || negb (edit_edge_openb t start)).
Definition EditBlockBitCount (s t : list Z) (limit block bit : Z) : Z :=
  Zlength (filter (fun idx => Z.ltb idx limit &&
    EditBlockStartTest t idx block && edit_bit_atb s idx bit)
    (Zrange 0 (Zlength s))).
Definition EditSegmentPositionCount (seg : list Z) (limit block : Z) : Z :=
  Zlength (filter (fun idx => Z.ltb idx limit && Z.eqb (Znth idx seg 0) block)
    (Zrange 0 (Zlength seg))).
Definition EditMatchCount (s1 s2 : list Z) (n : Z) : Z :=
  Zlength (filter (fun idx => Z.eqb (Znth idx s1 0) (Znth idx s2 0)) (Zrange 0 n)).
Definition EditRegionPermutation (s t out : list Z) (n : Z) : Prop :=
  Zlength out = n /\ Forall (fun bit => bit = 0 \/ bit = 1) out /\
  forall block bit, 0 <= block < n -> (bit = 0 \/ bit = 1) ->
    EditBlockBitCount out t n block bit = EditBlockBitCount s t n block bit.
Definition EditMaximumMatches (s1 s2 t1 t2 : list Z) (n answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun outputs : list Z * list Z =>
      EditRegionPermutation s1 t1 (fst outputs) n /\
      EditRegionPermutation s2 t2 (snd outputs) n)
    (fun outputs => EditMatchCount (fst outputs) (snd outputs) n) answer.
Definition EditSegmentMeaning (t : list Z) (upto : Z) (seg : list Z) : Prop :=
  forall idx, 0 <= idx < upto -> EditBlockStart t idx (Znth idx seg 0).
Definition EditCountsMeaning (s t : list Z) (n upto : Z) (cnt0 cnt1 : list Z) : Prop :=
  (forall block, 0 <= block < n -> Znth block cnt0 0 = EditBlockBitCount s t upto block 0) /\
  (forall block, 0 <= block < n -> Znth block cnt1 0 = EditBlockBitCount s t upto block 1).
Definition EditBuildMeaning (s t : list Z) (n upto : Z) (seg cnt0 cnt1 : list Z) : Prop :=
  EditSegmentMeaning t upto seg /\ EditCountsMeaning s t n upto cnt0 cnt1.
Definition EditRemainingMeaning (seg1 seg2 : list Z) (i : Z)
  (full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  (forall block, 0 <= block < Zlength seg1 ->
    Znth block cnt10 0 + Znth block cnt11 0 =
    Znth block full10 0 + Znth block full11 0 - EditSegmentPositionCount seg1 i block) /\
  (forall block, 0 <= block < Zlength seg2 ->
    Znth block cnt20 0 + Znth block cnt21 0 =
    Znth block full20 0 + Znth block full21 0 - EditSegmentPositionCount seg2 i block).

Record EditScanState : Type := EditSnapshot {
  edit_scan_position : Z;
  edit_scan_answer : Z;
  edit_zero1 : list Z;
  edit_one1 : list Z;
  edit_zero2 : list Z;
  edit_one2 : list Z
}.
(** One consumption step.  This relation is not recursively defined;
    Relation_Operators.clos_refl_trans supplies all finite execution traces. *)
Inductive EditGreedyStep (seg1 seg2 : list Z) : EditScanState -> EditScanState -> Prop :=
| EditStep_common_zero : forall i ans c10 c11 c20 c21 a b,
    0 <= i < Zlength seg1 -> Zlength seg2 = Zlength seg1 ->
    a = Znth i seg1 0 -> b = Znth i seg2 0 ->
    0 < Znth a c10 0 -> 0 < Znth b c20 0 ->
    EditGreedyStep seg1 seg2 (EditSnapshot i ans c10 c11 c20 c21)
      (EditSnapshot (i + 1) (ans + 1)
        (replace_Znth a (Znth a c10 0 - 1) c10) c11
        (replace_Znth b (Znth b c20 0 - 1) c20) c21)
| EditStep_common_one : forall i ans c10 c11 c20 c21 a b,
    0 <= i < Zlength seg1 -> Zlength seg2 = Zlength seg1 ->
    a = Znth i seg1 0 -> b = Znth i seg2 0 ->
    ~ (0 < Znth a c10 0 /\ 0 < Znth b c20 0) ->
    0 < Znth a c11 0 -> 0 < Znth b c21 0 ->
    EditGreedyStep seg1 seg2 (EditSnapshot i ans c10 c11 c20 c21)
      (EditSnapshot (i + 1) (ans + 1) c10
        (replace_Znth a (Znth a c11 0 - 1) c11) c20
        (replace_Znth b (Znth b c21 0 - 1) c21))
| EditStep_zero_one : forall i ans c10 c11 c20 c21 a b,
    0 <= i < Zlength seg1 -> Zlength seg2 = Zlength seg1 ->
    a = Znth i seg1 0 -> b = Znth i seg2 0 ->
    ~ (0 < Znth a c10 0 /\ 0 < Znth b c20 0) ->
    ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) ->
    0 < Znth a c10 0 -> 0 < Znth b c21 0 ->
    EditGreedyStep seg1 seg2 (EditSnapshot i ans c10 c11 c20 c21)
      (EditSnapshot (i + 1) ans (replace_Znth a (Znth a c10 0 - 1) c10)
        c11 c20 (replace_Znth b (Znth b c21 0 - 1) c21))
| EditStep_one_zero : forall i ans c10 c11 c20 c21 a b,
    0 <= i < Zlength seg1 -> Zlength seg2 = Zlength seg1 ->
    a = Znth i seg1 0 -> b = Znth i seg2 0 ->
    ~ (0 < Znth a c10 0 /\ 0 < Znth b c20 0) ->
    ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) ->
    ~ (0 < Znth a c10 0) -> 0 < Znth a c11 0 -> 0 < Znth b c20 0 ->
    EditGreedyStep seg1 seg2 (EditSnapshot i ans c10 c11 c20 c21)
      (EditSnapshot (i + 1) ans c10 (replace_Znth a (Znth a c11 0 - 1) c11)
        (replace_Znth b (Znth b c20 0 - 1) c20) c21).
Definition EditConsumedTrace (seg1 seg2 full10 full11 full20 full21 : list Z)
  (i answer : Z) (cnt10 cnt11 cnt20 cnt21 : list Z) : Prop :=
  Relation_Operators.clos_refl_trans EditScanState (EditGreedyStep seg1 seg2)
    (EditSnapshot 0 0 full10 full11 full20 full21)
    (EditSnapshot i answer cnt10 cnt11 cnt20 cnt21).

(** Public problem specification. The C solver receives decoded binary digits;
    its contract maps them back to the original character codes 48 and 49.
    A legal edit exchanges adjacent characters only when both mask positions
    permit participation. The answer is the maximum number of equal positions
    among pairs of strings obtainable by finitely many such edits. *)
Require Import SetsClass.SetsClass.
Import Sets.

Definition EditSwapAt (xs : list Z) (i j : Z) : list Z :=
  replace_Znth j (Znth i xs 0) (replace_Znth i (Znth j xs 0) xs).

Definition EditLegalSwap (mask before after : list Z) : Prop :=
  exists i : Z,
    0 <= i /\ i + 1 < Zlength before /\
    Znth i mask 0 = 49 /\ Znth (i + 1) mask 0 = 49 /\
    after = EditSwapAt before i (i + 1).

Definition EditPairMatches (left right : list Z) : Z :=
  Zlength (filter (fun p => Z.eqb (fst p) (snd p)) (combine left right)).

Definition EditStringsAnswer (s1 s2 t1 t2 : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun outputs : list Z * list Z =>
      SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap t1) s1 (fst outputs) /\
      SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap t2) s2 (snd outputs))
    (fun outputs => EditPairMatches (fst outputs) (snd outputs)) answer.

(** The following predicates describe feasible completions of the unprocessed
    suffix. They contain neither an execution trace nor a greedy-optimality
    assumption. Inventories use the C interface's decoded binary digits. *)
Definition EditInventoryCount (regions values : list Z) (block bit : Z) : Z :=
  Zlength (filter (fun p => Z.eqb (fst p) block && Z.eqb (snd p) bit)
    (combine regions values)).

Definition EditSuffixInventory (regions : list Z) (i : Z)
    (zeroes ones values : list Z) : Prop :=
  Zlength values = Zlength regions - i /\
  Forall (fun bit => bit = 0 \/ bit = 1) values /\
  forall block, 0 <= block < Zlength regions ->
    EditInventoryCount (sublist i (Zlength regions) regions) values block 0 = Znth block zeroes 0 /\
    EditInventoryCount (sublist i (Zlength regions) regions) values block 1 = Znth block ones 0.

Definition EditCompletion (s1 s2 t1 t2 prefix1 prefix2 : list Z)
    (outputs : list Z * list Z) : Prop :=
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap (map (Z.add 48) t1))
    (map (Z.add 48) s1) (map (Z.add 48) (prefix1 ++ fst outputs)) /\
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap (map (Z.add 48) t2))
    (map (Z.add 48) s2) (map (Z.add 48) (prefix2 ++ snd outputs)).

Definition EditFeasibleSuffix (s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 : list Z)
    (i : Z) (zeroes1 ones1 zeroes2 ones2 : list Z) (outputs : list Z * list Z) : Prop :=
  EditCompletion s1 s2 t1 t2 prefix1 prefix2 outputs /\
  EditSuffixInventory regions1 i zeroes1 ones1 (fst outputs) /\
  EditSuffixInventory regions2 i zeroes2 ones2 (snd outputs).

Definition EditRemainingMatches (s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 : list Z)
    (i : Z) (zeroes1 ones1 zeroes2 ones2 : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (EditFeasibleSuffix s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 i zeroes1 ones1 zeroes2 ones2)
    (fun outputs => EditPairMatches (fst outputs) (snd outputs)) answer.

Require Import Coq.Logic.Classical_Prop.
Require Import AUXLib.MonotonicList.

Lemma edit_pair_cons a b xs ys :
  EditPairMatches (a :: xs) (b :: ys) = Z.b2z (Z.eqb a b) + EditPairMatches xs ys.
Proof.
  unfold EditPairMatches. cbn [combine filter fst snd]. destruct (Z.eqb a b);
    rewrite ?Zlength_cons; cbn [Z.b2z]; lia.
Qed.
Lemma edit_pair_symmetric xs ys : EditPairMatches xs ys = EditPairMatches ys xs.
Proof.
  revert ys. induction xs as [|a xs IH]; intros [|b ys]; try reflexivity.
  rewrite !edit_pair_cons, Z.eqb_sym, IH; reflexivity.
Qed.
Lemma edit_pair_bounds xs ys : 0 <= EditPairMatches xs ys <= Zlength xs.
Proof.
  revert ys. induction xs as [|a xs IH]; intros [|b ys].
  - change (0 <= 0 <= 0); lia.
  - change (0 <= 0 <= 0); lia.
  - change (0 <= 0 <= Zlength (a :: xs)); split; [lia|apply Zlength_nonneg].
  - rewrite edit_pair_cons, Zlength_cons. specialize (IH ys).
    destruct (Z.eqb a b); cbn [Z.b2z]; lia.
Qed.
Lemma edit_pair_encode xs ys :
  EditPairMatches (map (Z.add 48) xs) (map (Z.add 48) ys) = EditPairMatches xs ys.
Proof.
  revert ys. induction xs as [|a xs IH]; intros [|b ys]; try reflexivity.
  cbn [map]. rewrite !edit_pair_cons, IH.
  destruct (Z.eqb_spec a b), (Z.eqb_spec (48 + a) (48 + b)); simpl; try lia.
Qed.
Lemma edit_pair_update_left xs ys i value :
  Zlength xs = Zlength ys -> 0 <= i < Zlength xs ->
  EditPairMatches (replace_Znth i value xs) ys =
    EditPairMatches xs ys - Z.b2z (Z.eqb (Znth i xs 0) (Znth i ys 0)) +
    Z.b2z (Z.eqb value (Znth i ys 0)).
Proof.
  revert ys i. induction xs as [|a xs IH]; intros [|b ys] i Hlen Hi;
    rewrite ?Zlength_cons, ?Zlength_nil in *; try lia; try (pose proof (Zlength_nonneg xs); lia).
  destruct (Z.eq_dec i 0) as [->|Hne].
  - change (EditPairMatches (value :: xs) (b :: ys) =
      EditPairMatches (a :: xs) (b :: ys) - Z.b2z (Z.eqb a b) + Z.b2z (Z.eqb value b)).
    rewrite !edit_pair_cons; lia.
  - rewrite replace_Znth_cons by lia. rewrite !edit_pair_cons, !Znth_cons by lia.
    rewrite IH by lia. lia.
Qed.
Lemma edit_pair_swap_left xs ys j :
  Zlength xs = Zlength ys -> 0 < j < Zlength xs ->
  EditPairMatches (EditSwapAt xs 0 j) ys = EditPairMatches xs ys -
    Z.b2z (Z.eqb (Znth 0 xs 0) (Znth 0 ys 0)) -
    Z.b2z (Z.eqb (Znth j xs 0) (Znth j ys 0)) +
    Z.b2z (Z.eqb (Znth j xs 0) (Znth 0 ys 0)) +
    Z.b2z (Z.eqb (Znth 0 xs 0) (Znth j ys 0)).
Proof.
  intros Hlen Hj. unfold EditSwapAt.
  rewrite !edit_pair_update_left by (rewrite ?Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff by lia. lia.
Qed.
Lemma edit_pair_swap_improves xs ys j :
  Zlength xs = Zlength ys -> 0 < j < Zlength xs ->
  Znth 0 xs 0 <> Znth 0 ys 0 -> Znth j xs 0 = Znth 0 ys 0 ->
  EditPairMatches xs ys <= EditPairMatches (EditSwapAt xs 0 j) ys.
Proof.
  intros Hlen Hj Hneq Heq. rewrite edit_pair_swap_left by auto.
  rewrite Heq, Z.eqb_refl. rewrite (proj2 (Z.eqb_neq _ _) Hneq).
  destruct (Z.eqb (Znth 0 ys 0) (Znth j ys 0));
    destruct (Z.eqb (Znth 0 xs 0) (Znth j ys 0)); cbn; lia.
Qed.
Lemma edit_inventory_cons region bit regions values block target :
  EditInventoryCount (region :: regions) (bit :: values) block target =
  Z.b2z (Z.eqb region block && Z.eqb bit target) + EditInventoryCount regions values block target.
Proof.
  unfold EditInventoryCount; cbn [combine filter fst snd].
  destruct (Z.eqb region block && Z.eqb bit target); rewrite ?Zlength_cons; cbn [Z.b2z]; lia.
Qed.
Lemma edit_inventory_update regions values i bit block target :
  Zlength regions = Zlength values -> 0 <= i < Zlength values ->
  EditInventoryCount regions (replace_Znth i bit values) block target =
  EditInventoryCount regions values block target -
    Z.b2z (Z.eqb (Znth i regions 0) block && Z.eqb (Znth i values 0) target) +
    Z.b2z (Z.eqb (Znth i regions 0) block && Z.eqb bit target).
Proof.
  revert values i. induction regions as [|r regions IH]; intros [|v values] i Hlen Hi;
    rewrite ?Zlength_cons, ?Zlength_nil in *; try lia; try (pose proof (Zlength_nonneg regions); lia);
    try (pose proof (Zlength_nonneg values); lia).
  destruct (Z.eq_dec i 0) as [->|Hne].
  - change (EditInventoryCount (r :: regions) (bit :: values) block target =
      EditInventoryCount (r :: regions) (v :: values) block target -
      Z.b2z (Z.eqb r block && Z.eqb v target) + Z.b2z (Z.eqb r block && Z.eqb bit target)).
    rewrite !edit_inventory_cons; lia.
  - rewrite replace_Znth_cons by lia. rewrite !edit_inventory_cons, !Znth_cons by lia.
    rewrite IH by lia. lia.
Qed.
Lemma edit_inventory_swap regions values i j block bit :
  Zlength regions = Zlength values -> 0 <= i < Zlength values -> 0 <= j < Zlength values ->
  Znth i regions 0 = Znth j regions 0 ->
  EditInventoryCount regions (EditSwapAt values i j) block bit =
  EditInventoryCount regions values block bit.
Proof.
  intros Hlen Hi Hj Hsame. unfold EditSwapAt.
  destruct (Z.eq_dec i j) as [->|Hne].
  - rewrite !replace_Znth_Znth; reflexivity.
  - rewrite !edit_inventory_update by (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia. rewrite Hsame; lia.
Qed.

Lemma edit_bounded_maximum {A} (candidates : A -> Prop) (score : A -> Z) bound :
  (exists x, candidates x) ->
  (forall x, candidates x -> 0 <= score x <= bound) ->
  exists answer, max_value_of_subset Z.le candidates score answer.
Proof.
  assert (Hmain : forall b, 0 <= b ->
    (exists x, candidates x) ->
    (forall x, candidates x -> 0 <= score x <= b) ->
    exists answer, max_value_of_subset Z.le candidates score answer).
  { apply (Z_lt_induction (fun b =>
      (exists x, candidates x) ->
      (forall x, candidates x -> 0 <= score x <= b) ->
      exists answer, max_value_of_subset Z.le candidates score answer)).
    intros b IH Hinh Hbounds.
    destruct (classic (exists x, candidates x /\ score x = b)) as [[x [Hx Heq]]|Hnot].
    - exists b. exists x. split; [split; [exact Hx|]|exact Heq].
      intros y Hy. specialize (Hbounds y Hy). lia.
    - assert (Hsmaller : forall x, candidates x -> 0 <= score x <= b - 1).
      { intros x Hx. specialize (Hbounds x Hx).
        assert (score x <> b) by (intro H; apply Hnot; exists x; auto). lia. }
      destruct Hinh as [x Hx]. pose proof (Hsmaller x Hx) as Hb.
      apply (IH (b - 1) ltac:(lia)); [exists x; exact Hx|exact Hsmaller]. }
  intros Hinh Hbounds. destruct Hinh as [x Hx]. pose proof (Hbounds x Hx) as Hb.
  apply (Hmain bound ltac:(lia)); [exists x; exact Hx|exact Hbounds].
Qed.
Lemma edit_map_length {A B} (f : A -> B) xs : Zlength (map f xs) = Zlength xs.
Proof. rewrite !Zlength_correct, length_map; reflexivity. Qed.
Lemma edit_map_replace {A B} (f : A -> B) xs i x :
  map f (replace_Znth i x xs) = replace_Znth i (f x) (map f xs).
Proof.
  unfold replace_Znth. generalize (Z.to_nat i) as k.
  induction xs; intros [|k]; cbn; auto. rewrite IHxs; reflexivity.
Qed.
Lemma edit_map_read {A B} (f : A -> B) xs i da db :
  0 <= i < Zlength xs -> Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros Hi. unfold Znth.
  replace (nth (Z.to_nat i) (map f xs) db) with (nth (Z.to_nat i) (map f xs) (f da)).
  - apply map_nth.
  - apply nth_indep. rewrite length_map. rewrite Zlength_correct in Hi; lia.
Qed.
Lemma edit_swap_length xs i j : Zlength (EditSwapAt xs i j) = Zlength xs.
Proof. unfold EditSwapAt. rewrite !Zlength_replace_Znth; reflexivity. Qed.
Lemma edit_swap_read xs i j k :
  0 <= i < Zlength xs -> 0 <= j < Zlength xs -> 0 <= k < Zlength xs ->
  Znth k (EditSwapAt xs i j) 0 =
  if Z.eqb k j then Znth i xs 0 else if Z.eqb k i then Znth j xs 0 else Znth k xs 0.
Proof.
  intros Hi Hj Hk. unfold EditSwapAt.
  destruct (Z.eqb_spec k j) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia); reflexivity.
  - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    destruct (Z.eqb_spec k i) as [->|Hne'];
      [rewrite Znth_replace_Znth_Same|rewrite Znth_replace_Znth_Diff]; auto; lia.
Qed.
Lemma edit_swap_encode xs i j :
  0 <= i < Zlength xs -> 0 <= j < Zlength xs ->
  map (Z.add 48) (EditSwapAt xs i j) = EditSwapAt (map (Z.add 48) xs) i j.
Proof.
  intros Hi Hj. unfold EditSwapAt. rewrite !edit_map_replace.
  rewrite !edit_map_read with (da := 0) by lia; reflexivity.
Qed.
Lemma edit_Forall_replace {A} (P : A -> Prop) xs i x :
  Forall P xs -> P x -> Forall P (replace_Znth i x xs).
Proof.
  intros Hxs Hx. unfold replace_Znth. generalize (Z.to_nat i) as k.
  induction Hxs; intros [|k]; cbn; constructor; auto.
Qed.
Lemma edit_Forall_swap (P : Z -> Prop) xs i j :
  Forall P xs -> 0 <= i < Zlength xs -> 0 <= j < Zlength xs ->
  Forall P (EditSwapAt xs i j).
Proof.
  intros Hxs Hi Hj. unfold EditSwapAt. apply edit_Forall_replace.
  - apply edit_Forall_replace; [exact Hxs|]. apply (proj1 (Forall_Znth P 0 xs) Hxs j Hj).
  - apply (proj1 (Forall_Znth P 0 xs) Hxs i Hi).
Qed.
Lemma edit_closure_preserves {A} (step : A -> A -> Prop) (P : A -> Prop) :
  (forall x y, step x y -> P x -> P y) ->
  forall x y, SetsClass.RelsDomain.clos_refl_trans step x y -> P x -> P y.
Proof.
  intros Hstep x y [n Hn]. revert x y Hn.
  induction n as [|n IH]; intros x y Hn Hx.
  - change (x = y) in Hn. subst y; exact Hx.
  - change (exists z, step x z /\ nsteps step n z y) in Hn.
    destruct Hn as [z [Hxz Hzy]]. eapply IH; [exact Hzy|]. eapply Hstep; eauto.
Qed.
Lemma edit_legal_length mask before after :
  EditLegalSwap mask before after -> Zlength after = Zlength before.
Proof. intros [i (_ & _ & _ & _ & ->)]. apply edit_swap_length. Qed.
Lemma edit_reachable_length mask before after :
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) before after ->
  Zlength after = Zlength before.
Proof.
  intros H. eapply (edit_closure_preserves (EditLegalSwap mask) (fun xs => Zlength xs = Zlength before));
    [|exact H|reflexivity].
  intros x y Hstep Hx. rewrite (edit_legal_length _ _ _ Hstep); exact Hx.
Qed.
Lemma edit_reachable_Forall mask before after (P : Z -> Prop) :
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) before after ->
  Forall P before -> Forall P after.
Proof.
  intros H Hbefore. eapply (edit_closure_preserves (EditLegalSwap mask) (Forall P));
    [|exact H|exact Hbefore].
  intros x y [i (Hi & Hj & _ & _ & ->)] Hx. apply edit_Forall_swap; auto; lia.
Qed.
Lemma edit_reachable_step mask before after :
  EditLegalSwap mask before after ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) before after.
Proof. intros H. exists 1%nat. change (exists z, EditLegalSwap mask before z /\ z = after). exists after; auto. Qed.

Lemma edit_swap_conjugate xs i p j :
  0 <= i < p -> p < j < Zlength xs ->
  EditSwapAt (EditSwapAt (EditSwapAt xs i p) p j) i p = EditSwapAt xs i j.
Proof.
  intros Hip Hpj. apply (proj2 (list_eq_ext _ _ 0)); split.
  - rewrite !edit_swap_length; reflexivity.
  - intros k Hk. rewrite !edit_swap_length in Hk.
    repeat rewrite edit_swap_read by (rewrite ?edit_swap_length; lia).
    repeat match goal with |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); subst; try lia end; reflexivity.
Qed.
Lemma edit_swap_reachable mask xs i j :
  0 <= i <= j -> j < Zlength xs ->
  (forall k, i <= k <= j -> Znth k mask 0 = 49) ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) xs (EditSwapAt xs i j).
Proof.
  assert (Hmain : forall d, 0 <= d -> forall values lo hi,
    hi - lo = d -> 0 <= lo <= hi -> hi < Zlength values ->
    (forall k, lo <= k <= hi -> Znth k mask 0 = 49) ->
    SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) values (EditSwapAt values lo hi)).
  { apply (Z_lt_induction (fun d => forall values lo hi,
      hi - lo = d -> 0 <= lo <= hi -> hi < Zlength values ->
      (forall k, lo <= k <= hi -> Znth k mask 0 = 49) ->
      SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) values (EditSwapAt values lo hi))).
    intros d IH values lo hi Hd Hlo Hhi Hmask.
    destruct (Z.eq_dec lo hi) as [->|Hne].
    - unfold EditSwapAt. rewrite !replace_Znth_Znth. reflexivity.
    - destruct (Z.eq_dec hi (lo + 1)) as [->|Hfar].
      + apply edit_reachable_step. exists lo. repeat split; try lia; try reflexivity; apply Hmask; lia.
      + rewrite <- (edit_swap_conjugate values lo (lo + 1) hi ltac:(lia) ltac:(lia)).
        eapply (rt2_trans_ins (list Z) (EditLegalSwap mask) values
          (EditSwapAt values lo (lo + 1))).
        * apply edit_reachable_step. exists lo. repeat split; try lia; try reflexivity; apply Hmask; lia.
        * eapply (rt2_trans_ins (list Z) (EditLegalSwap mask)
            (EditSwapAt values lo (lo + 1))
            (EditSwapAt (EditSwapAt values lo (lo + 1)) (lo + 1) hi)).
          -- apply (IH (d - 1) ltac:(lia)); try lia.
             ++ rewrite edit_swap_length; lia.
             ++ intros k Hk; apply Hmask; lia.
          -- apply edit_reachable_step. exists lo. repeat split; try reflexivity;
               try lia; try (rewrite !edit_swap_length; lia); apply Hmask; lia. }
  intros Hi Hj Hmask. apply (Hmain (j - i) ltac:(lia)); auto.
Qed.

(** Reused representation lemmas from the backed-up manual. *)
Lemma edit_interval_library : forall lo hi,
  edit_zrange_between lo hi = Zrange lo hi.
Proof.
  intros lo hi. unfold edit_zrange_between, Zrange.
  remember (Z.to_nat (hi - lo)) as count. clear Heqcount hi. revert lo.
  induction count as [|count IH]; intros lo; simpl; [reflexivity |].
  rewrite Z.add_0_r. f_equal. rewrite <- seq_shift, map_map.
  rewrite <- IH. apply map_ext. intros x. lia.
Qed.
Lemma edit_range_library : forall n, edit_zrange n = Zrange 0 n.
Proof.
  intros n. assert (H : edit_zrange n = edit_zrange_between 0 n).
  { unfold edit_zrange, edit_zrange_between. rewrite Z.sub_0_r. reflexivity. }
  rewrite H, edit_interval_library. reflexivity.
Qed.
Lemma edit_open_edges_eq : forall t lo hi,
  edit_all_edges_openb t lo hi = EditOpenEdgesTest t lo hi.
Proof. intros. unfold edit_all_edges_openb, EditOpenEdgesTest. rewrite edit_interval_library. reflexivity. Qed.
Lemma edit_block_test_eq : forall t idx block,
  edit_block_startb t idx block = EditBlockStartTest t idx block.
Proof. intros. unfold edit_block_startb, EditBlockStartTest. rewrite edit_open_edges_eq. reflexivity. Qed.
Lemma edit_block_bit_count_eq : forall s t limit block bit,
  edit_count_bit_in_block_prefix s t limit block bit = EditBlockBitCount s t limit block bit.
Proof.
  intros. unfold edit_count_bit_in_block_prefix, EditBlockBitCount.
  rewrite !Zlength_correct, edit_range_library. f_equal. f_equal.
  apply filter_ext_in. intros idx _. rewrite edit_block_test_eq. reflexivity.
Qed.
Lemma edit_position_count_eq : forall seg limit block,
  edit_count_positions_in_seg_prefix seg limit block = EditSegmentPositionCount seg limit block.
Proof. intros. unfold edit_count_positions_in_seg_prefix, EditSegmentPositionCount. rewrite !Zlength_correct, edit_range_library. reflexivity. Qed.
Lemma edit_match_count_eq : forall s1 s2 n,
  edit_match_count s1 s2 n = EditMatchCount s1 s2 n.
Proof. intros. unfold edit_match_count, EditMatchCount. rewrite !Zlength_correct, edit_range_library. reflexivity. Qed.
Lemma edit_binary_alphabet_iff : forall xs n,
  EditBinaryList xs n <-> Zlength xs = n /\ Forall (fun bit => bit = 0 \/ bit = 1) xs.
Proof.
  intros xs n. unfold EditBinaryList.
  rewrite (Forall_Znth (fun bit => bit = 0 \/ bit = 1) 0 xs).
  split; intros [Hlen H]; (split; [exact Hlen | intros idx Hi; apply H; lia]).
Qed.
Lemma edit_bounds_iff : forall xs lo hi,
  (Forall (Z.le lo) xs /\ Forall (Z.ge hi) xs) <->
  (forall idx, 0 <= idx < Zlength xs -> lo <= Znth idx xs 0 <= hi).
Proof.
  intros xs lo hi. split.
  - intros [Hl Hh] idx Hi.
    pose proof (proj1 (Forall_Znth (Z.le lo) 0 xs) Hl idx Hi) as H1.
    pose proof (proj1 (Forall_Znth (Z.ge hi) 0 xs) Hh idx Hi) as H2.
    apply Z.ge_le in H2. lia.
  - intros H. split.
    + apply (proj2 (Forall_Znth (Z.le lo) 0 xs)). intros idx Hi. specialize (H idx Hi). lia.
    + apply (proj2 (Forall_Znth (Z.ge hi) 0 xs)). intros idx Hi. specialize (H idx Hi). apply Z.le_ge. lia.
Qed.
Lemma edit_binary_iff : forall xs n,
  EditBinaryList xs n <-> Zlength xs = n /\ Forall (Z.le 0) xs /\ Forall (Z.ge 1) xs.
Proof.
  intros xs n. unfold EditBinaryList. rewrite edit_bounds_iff.
  split; intros [Hlen H]; (split; [exact Hlen | intros idx Hi; specialize (H idx ltac:(lia)); lia]).
Qed.
Lemma edit_zero_prefix_iff : forall xs written,
  EditZeroPrefix xs written <-> Zlength xs = written /\ Forall (eq 0) xs.
Proof.
  intros xs written. unfold EditZeroPrefix. rewrite (Forall_Znth (eq 0) 0 xs).
  split; intros [Hlen H]; (split; [exact Hlen | intros idx Hi; specialize (H idx ltac:(lia)); lia]).
Qed.
Lemma edit_zero_full_iff : forall n xs,
  EditZeroFull n xs <-> Zlength xs = n /\ Forall (eq 0) xs.
Proof. intros. exact (edit_zero_prefix_iff xs n). Qed.
Lemma edit_count_bounds_iff : forall n cnt,
  EditCountBounds n cnt <-> Zlength cnt = n /\ Forall (Z.le 0) cnt /\ Forall (Z.ge n) cnt.
Proof.
  intros n cnt. unfold EditCountBounds. rewrite edit_bounds_iff.
  split; intros [Hlen H]; (split; [exact Hlen | intros idx Hi; apply H; lia]).
Qed.
Lemma edit_segment_iff : forall t upto seg,
  EditSegmentPrefix t upto seg <-> Zlength seg = upto /\ EditSegmentMeaning t upto seg.
Proof. intros. unfold EditSegmentPrefix, EditSegmentMeaning. tauto. Qed.
Lemma edit_counts_iff : forall s t n upto cnt0 cnt1,
  EditCountsForPrefix s t n upto cnt0 cnt1 <->
  Zlength cnt0 = n /\ Zlength cnt1 = n /\ EditCountsMeaning s t n upto cnt0 cnt1.
Proof.
  intros. unfold EditCountsForPrefix, EditCountsMeaning.
  setoid_rewrite edit_block_bit_count_eq. tauto.
Qed.
Lemma edit_build_iff : forall s t n upto seg cnt0 cnt1,
  EditBuildState s t n upto seg cnt0 cnt1 <->
  0 <= upto /\ upto <= n /\
  Zlength s = n /\ Forall (Z.le 0) s /\ Forall (Z.ge 1) s /\
  Zlength t = n /\ Forall (Z.le 0) t /\ Forall (Z.ge 1) t /\
  Zlength seg = upto /\ Zlength cnt0 = n /\ Zlength cnt1 = n /\
  EditBuildMeaning s t n upto seg cnt0 cnt1.
Proof.
  intros. unfold EditBuildState, EditBuildMeaning.
  rewrite !edit_binary_iff, edit_segment_iff, edit_counts_iff. tauto.
Qed.

Lemma edit_filter_count {A} (test : A -> bool) xs :
  Zlength (filter test xs) = AUXLib.ListLib.sum (map (fun x => Z.b2z (test x)) xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. cbn [filter map].
  destruct (test x); rewrite ?Zlength_cons; cbn [AUXLib.ListLib.sum fold_right Z.b2z];
    unfold AUXLib.ListLib.sum in IH; lia.
Qed.
Lemma edit_inventory_range regions values block bit :
  EditInventoryCount regions values block bit =
  SumLib.Sum.sum (fun i => 0 <= i < Z.min (Zlength regions) (Zlength values))
    (fun i => Z.b2z (Z.eqb (Znth i regions 0) block && Z.eqb (Znth i values 0) bit)).
Proof.
  unfold EditInventoryCount. rewrite edit_filter_count.
  exact (list_sum_map_combine_as_Z_range_sum 0 0
    (fun r v => Z.b2z (Z.eqb r block && Z.eqb v bit)) regions values).
Qed.
Lemma edit_block_count_range s t limit block bit :
  EditBlockBitCount s t limit block bit =
  SumLib.Sum.sum (fun i => 0 <= i < Zlength s)
    (fun i => Z.b2z (Z.ltb i limit && EditBlockStartTest t i block && edit_bit_atb s i bit)).
Proof.
  unfold EditBlockBitCount. rewrite edit_filter_count, sum_range_unfold.
  unfold AUXLib.ListLib.sum.
  induction (Zrange 0 (Zlength s)); cbn [map fold_right]; congruence.
Qed.
Lemma edit_block_test_segment t seg n i block :
  EditSegmentMeaning t n seg -> 0 <= i < n ->
  EditBlockStartTest t i block = Z.eqb (Znth i seg 0) block.
Proof.
  intros Hseg Hi. specialize (Hseg i Hi).
  destruct (EditBlockStartTest t i block) eqn:Htest;
    destruct (Z.eqb (Znth i seg 0) block) eqn:Heq; try reflexivity.
  - rewrite <- edit_block_test_eq in Htest.
    apply edit_block_startb_true_iff__build_s1_segments_counts in Htest.
    pose proof (edit_block_start_unique__build_s2_segments_counts t i _ _ Hseg Htest).
    apply Z.eqb_neq in Heq; contradiction.
  - apply Z.eqb_eq in Heq. rewrite <- Heq in Htest.
    rewrite <- edit_block_test_eq in Htest.
    apply edit_block_startb_true_iff__build_s1_segments_counts in Hseg.
    rewrite Hseg in Htest; discriminate.
Qed.
Lemma edit_full_inventory s t seg n block bit :
  Zlength s = n -> Zlength seg = n -> EditSegmentMeaning t n seg ->
  EditBlockBitCount s t n block bit = EditInventoryCount seg s block bit.
Proof.
  intros Hs Hseg Hmeaning. rewrite edit_inventory_range, edit_block_count_range.
  rewrite Hs, Hseg, Z.min_id. apply sum_Z_range_ext. intros i Hi.
  rewrite (edit_block_test_segment t seg n i block Hmeaning Hi).
  rewrite (proj2 (Z.ltb_lt i n) ltac:(lia)). cbn [andb]. reflexivity.
Qed.
Lemma edit_region_between t seg n i j k :
  EditSegmentMeaning t n seg -> 0 <= i <= j -> j <= k < n ->
  Znth i seg 0 = Znth k seg 0 -> Znth j seg 0 = Znth i seg 0.
Proof.
  intros Hseg Hij Hjk Heq.
  pose proof (Hseg i ltac:(lia)) as [[Hstart Hbound] _].
  pose proof (Hseg k ltac:(lia)) as Hk. rewrite <- Heq in Hk.
  destruct Hk as [_ [Hedges Hboundary]].
  eapply edit_block_start_unique__build_s2_segments_counts; [apply Hseg; lia|].
  split; [lia|]. split; [intros q Hq; apply Hedges; lia|exact Hboundary].
Qed.
Lemma edit_region_open t seg n i j :
  Zlength t = n -> EditSegmentMeaning t n seg -> 0 <= i < j -> j < n ->
  Znth i seg 0 = Znth j seg 0 ->
  forall k, i <= k <= j -> Znth k (map (Z.add 48) t) 0 = 49.
Proof.
  intros Ht Hseg Hij Hjn Heq k Hk.
  pose proof (Hseg i ltac:(lia)) as [[Hstart Hbound] _].
  pose proof (Hseg j ltac:(lia)) as Hj. rewrite <- Heq in Hj.
  destruct Hj as [_ [Hedges _]]. rewrite edit_map_read with (da := 0) by lia.
  destruct (Z.eq_dec k i) as [->|Hne].
  - pose proof (Hedges (i + 1) ltac:(lia)) as [Hleft _].
    unfold edit_edge_open in Hleft. replace (i + 1 - 1) with i in Hleft by lia. lia.
  - pose proof (Hedges k ltac:(lia)) as [_ Hright]. lia.
Qed.

Lemma edit_eqb_shift c x y : Z.eqb (c + x) (c + y) = Z.eqb x y.
Proof. destruct (Z.eqb_spec (c + x) (c + y)), (Z.eqb_spec x y); try reflexivity; lia. Qed.
Lemma edit_encode_decode xs : map (Z.add 48) (map (Z.add (-48)) xs) = xs.
Proof. induction xs; cbn [map]; f_equal; auto; lia. Qed.
Lemma edit_pair_decode xs ys :
  EditPairMatches (map (Z.add (-48)) xs) (map (Z.add (-48)) ys) = EditPairMatches xs ys.
Proof.
  pose proof (edit_pair_encode (map (Z.add (-48)) xs) (map (Z.add (-48)) ys)) as H.
  rewrite !edit_encode_decode in H; symmetry; exact H.
Qed.
Lemma edit_inventory_encode regions values block bit :
  EditInventoryCount regions (map (Z.add 48) values) block (48 + bit) =
  EditInventoryCount regions values block bit.
Proof.
  revert values. induction regions as [|r regions IH]; intros [|v values]; try reflexivity.
  cbn [map]. rewrite !edit_inventory_cons, edit_eqb_shift, IH; reflexivity.
Qed.
Lemma edit_encode_alphabet xs :
  Forall (fun x => x = 0 \/ x = 1) xs ->
  Forall (fun x => x = 48 \/ x = 49) (map (Z.add 48) xs).
Proof.
  rewrite Forall_map. intros H. eapply Forall_impl; [|exact H]. intros x [-> | ->]; cbn; auto.
Qed.
Lemma edit_decode_alphabet xs :
  Forall (fun x => x = 48 \/ x = 49) xs ->
  Forall (fun x => x = 0 \/ x = 1) (map (Z.add (-48)) xs).
Proof.
  rewrite Forall_map. intros H. eapply Forall_impl; [|exact H]. intros x [-> | ->]; cbn; auto.
Qed.
Lemma edit_regions_edges t seg n :
  Zlength t = n -> Zlength seg = n -> EditSegmentMeaning t n seg ->
  forall i, 0 <= i -> i + 1 < Zlength seg ->
    Znth i (map (Z.add 48) t) 0 = 49 -> Znth (i + 1) (map (Z.add 48) t) 0 = 49 ->
    Znth i seg 0 = Znth (i + 1) seg 0.
Proof.
  intros Ht Hseg Hmeaning i Hi Hin Hleft Hright.
  rewrite edit_map_read with (da := 0) in Hleft, Hright by lia.
  assert (Hedge : edit_edge_open t (i + 1)).
  { unfold edit_edge_open. replace (i + 1 - 1) with i by lia. split; lia. }
  pose proof (Hmeaning i ltac:(lia)) as [Hstart [Hedges Hboundary]].
  eapply edit_block_start_unique__build_s2_segments_counts; [|apply Hmeaning; lia].
  split; [lia|]. split; [|exact Hboundary].
  intros k Hk. destruct (Z.eq_dec k (i + 1)) as [->|Hne]; [exact Hedge|]. apply Hedges; lia.
Qed.
Lemma edit_reachable_inventory regions mask before after :
  Zlength regions = Zlength before ->
  (forall i, 0 <= i -> i + 1 < Zlength regions ->
    Znth i mask 0 = 49 -> Znth (i + 1) mask 0 = 49 ->
    Znth i regions 0 = Znth (i + 1) regions 0) ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap mask) before after ->
  forall block bit, EditInventoryCount regions after block bit = EditInventoryCount regions before block bit.
Proof.
  intros Hlength Hedges Hreach block bit.
  assert (Hpreserve : Zlength after = Zlength regions /\
    EditInventoryCount regions after block bit = EditInventoryCount regions before block bit).
  { eapply (edit_closure_preserves (EditLegalSwap mask)
      (fun values => Zlength values = Zlength regions /\
        EditInventoryCount regions values block bit = EditInventoryCount regions before block bit));
      [|exact Hreach|split; [symmetry; exact Hlength|reflexivity]].
    intros xs ys [i (Hi & Hin & Hleft & Hright & ->)] [Hlen Hcount]. split.
    - rewrite edit_swap_length; exact Hlen.
    - rewrite edit_inventory_swap by (try lia; apply Hedges; auto; lia). exact Hcount. }
  exact (proj2 Hpreserve).
Qed.
Lemma edit_initial_inventory s t seg zeroes ones n output :
  Zlength s = n -> Zlength t = n -> Zlength seg = n ->
  Forall (fun bit => bit = 0 \/ bit = 1) s ->
  EditBuildMeaning s t n n seg zeroes ones ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap (map (Z.add 48) t))
    (map (Z.add 48) s) output ->
  EditSuffixInventory seg 0 zeroes ones (map (Z.add (-48)) output).
Proof.
  intros Hs Ht Hseg Hbinary [Hsegments [Hz Ho]] Hreach.
  pose proof (edit_reachable_length _ _ _ Hreach) as Houtlen. rewrite edit_map_length in Houtlen.
  unfold EditSuffixInventory. split.
  - rewrite edit_map_length; lia.
  - split.
    + apply edit_decode_alphabet. eapply edit_reachable_Forall; [exact Hreach|]. apply edit_encode_alphabet; exact Hbinary.
    + assert (Hcounts : forall block bit,
        EditInventoryCount seg (map (Z.add (-48)) output) block bit = EditBlockBitCount s t n block bit).
      { intros block bit.
        rewrite <- (edit_inventory_encode seg (map (Z.add (-48)) output) block bit), edit_encode_decode.
        rewrite (edit_reachable_inventory seg (map (Z.add 48) t) (map (Z.add 48) s) output
          ltac:(rewrite edit_map_length; lia)
          (edit_regions_edges t seg n Ht Hseg Hsegments) Hreach block (48 + bit)).
        rewrite edit_inventory_encode. symmetry. apply edit_full_inventory; auto. }
      intros block Hb. rewrite Hseg in Hb.
      rewrite sublist_self by reflexivity. rewrite !Hcounts. split; symmetry; [apply Hz|apply Ho]; lia.
Qed.
Lemma edit_answer_exists s1 s2 t1 t2 : exists answer, EditStringsAnswer s1 s2 t1 t2 answer.
Proof.
  unfold EditStringsAnswer. apply edit_bounded_maximum with (bound := Zlength s1).
  - exists (s1,s2); split; reflexivity.
  - intros [out1 out2] [H1 H2]. cbn [fst snd] in *.
    pose proof (edit_pair_bounds out1 out2) as Hb.
    pose proof (edit_reachable_length _ _ _ H1) as Hlen. lia.
Qed.
Lemma edit_initial_remaining s1 s2 t1 t2 seg1 seg2 c10 c11 c20 c21 n :
  Zlength s1 = n -> Zlength s2 = n -> Zlength t1 = n -> Zlength t2 = n ->
  Zlength seg1 = n -> Zlength seg2 = n ->
  Forall (fun bit => bit = 0 \/ bit = 1) s1 -> Forall (fun bit => bit = 0 \/ bit = 1) s2 ->
  EditBuildMeaning s1 t1 n n seg1 c10 c11 -> EditBuildMeaning s2 t2 n n seg2 c20 c21 ->
  exists answer,
    EditRemainingMatches s1 s2 t1 t2 seg1 seg2 [] [] 0 c10 c11 c20 c21 answer /\
    EditStringsAnswer (map (Z.add 48) s1) (map (Z.add 48) s2)
      (map (Z.add 48) t1) (map (Z.add 48) t2) answer.
Proof.
  intros Hs1 Hs2 Ht1 Ht2 Hseg1 Hseg2 Hb1 Hb2 Hbuild1 Hbuild2.
  destruct (edit_answer_exists (map (Z.add 48) s1) (map (Z.add 48) s2)
    (map (Z.add 48) t1) (map (Z.add 48) t2)) as [answer Hanswer].
  exists answer; split; [|exact Hanswer].
  destruct Hanswer as [[out1 out2] [[[Hreach1 Hreach2] Hupper] Hvalue]]. cbn [fst snd] in *.
  pose proof (edit_initial_inventory s1 t1 seg1 c10 c11 n out1 Hs1 Ht1 Hseg1 Hb1 Hbuild1 Hreach1) as Hinv1.
  pose proof (edit_initial_inventory s2 t2 seg2 c20 c21 n out2 Hs2 Ht2 Hseg2 Hb2 Hbuild2 Hreach2) as Hinv2.
  exists (map (Z.add (-48)) out1, map (Z.add (-48)) out2). split; [split|].
  - split.
    + unfold EditCompletion; cbn [fst snd List.app]. rewrite !edit_encode_decode; auto.
    + cbn [fst snd]; auto.
  - intros [x y] [Hcompletion Hinv].
    unfold EditCompletion in Hcompletion; cbn [fst snd List.app] in Hcompletion.
    specialize (Hupper (map (Z.add 48) x, map (Z.add 48) y) Hcompletion).
    cbn [fst snd] in Hupper. rewrite edit_pair_encode in Hupper.
    cbn [fst snd]. rewrite edit_pair_decode. exact Hupper.
  - cbn [fst snd]. rewrite edit_pair_decode; exact Hvalue.
Qed.

Lemma edit_swap_prepend prefix values i j :
  0 <= i < Zlength values -> 0 <= j < Zlength values ->
  EditSwapAt (prefix ++ values) (Zlength prefix + i) (Zlength prefix + j) =
    prefix ++ EditSwapAt values i j.
Proof.
  intros Hi Hj. unfold EditSwapAt.
  rewrite !app_Znth2 by lia.
  replace (Zlength prefix + i - Zlength prefix) with i by lia.
  replace (Zlength prefix + j - Zlength prefix) with j by lia.
  rewrite (replace_Znth_app_r (Zlength prefix + i) _ prefix values) by lia.
  rewrite (replace_Znth_nothing (Zlength prefix + i) prefix) by lia.
  replace (Zlength prefix + i - Zlength prefix) with i by lia.
  rewrite (replace_Znth_app_r (Zlength prefix + j) _ prefix) by lia.
  rewrite (replace_Znth_nothing (Zlength prefix + j) prefix) by lia.
  replace (Zlength prefix + j - Zlength prefix) with j by lia. reflexivity.
Qed.
Lemma edit_extension_swap source t seg n prefix values i j :
  Zlength t = n -> EditSegmentMeaning t n seg ->
  Zlength prefix = i -> Zlength values = n - i -> 0 <= i < n -> 0 < j < Zlength values ->
  Znth (i + j) seg 0 = Znth i seg 0 ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap (map (Z.add 48) t))
    source (map (Z.add 48) (prefix ++ values)) ->
  SetsClass.RelsDomain.clos_refl_trans (EditLegalSwap (map (Z.add 48) t))
    source (map (Z.add 48) (prefix ++ EditSwapAt values 0 j)).
Proof.
  intros Ht Hseg Hp Hv Hi Hj Hsame Hreach.
  eapply (rt2_trans_ins (list Z) (EditLegalSwap (map (Z.add 48) t))
    source (map (Z.add 48) (prefix ++ values))); [exact Hreach|].
  rewrite <- (edit_swap_prepend prefix values 0 j ltac:(lia) ltac:(lia)).
  rewrite edit_swap_encode by (rewrite Zlength_app; pose proof (Zlength_nonneg prefix); lia).
  rewrite Hp, Z.add_0_r. apply edit_swap_reachable.
  - lia.
  - rewrite edit_map_length, Zlength_app; lia.
  - apply (edit_region_open t seg n i (i + j)); auto; lia.
Qed.
Lemma edit_suffix_swap regions i zeroes ones values j :
  0 <= i < Zlength regions -> EditSuffixInventory regions i zeroes ones values ->
  0 < j < Zlength values -> Znth (i + j) regions 0 = Znth i regions 0 ->
  EditSuffixInventory regions i zeroes ones (EditSwapAt values 0 j).
Proof.
  intros Hi [Hlen [Hbinary Hcounts]] Hj Hsame. split; [rewrite edit_swap_length; exact Hlen|].
  split; [apply edit_Forall_swap; auto; lia|].
  intros block Hb. rewrite !edit_inventory_swap; auto;
    try (rewrite Zlength_sublist; lia);
    try lia.
  all: rewrite !Znth_sublist by lia; replace (0 + i) with i by lia;
    replace (j + i) with (i + j) by lia; symmetry; exact Hsame.
Qed.
Lemma edit_feasible_swap_left s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n x y j :
  Zlength t1 = n -> Zlength seg1 = n -> EditSegmentMeaning t1 n seg1 ->
  Zlength prefix1 = i -> 0 <= i < n ->
  EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,y) ->
  0 < j < n - i -> Znth (i + j) seg1 0 = Znth i seg1 0 ->
  EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (EditSwapAt x 0 j,y).
Proof.
  intros Ht Hseg Hmeaning Hp Hi [Hcompletion [Hinv1 Hinv2]] Hj Hsame.
  pose proof (proj1 Hinv1) as Hxlen. cbn [fst snd] in Hxlen; rewrite Hseg in Hxlen.
  split.
  - destruct Hcompletion as [H1 H2]. split; [|exact H2].
    eapply edit_extension_swap; eauto; lia.
  - split; [|exact Hinv2]. apply edit_suffix_swap; auto; lia.
Qed.
Lemma edit_feasible_swap_right s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n x y j :
  Zlength t2 = n -> Zlength seg2 = n -> EditSegmentMeaning t2 n seg2 ->
  Zlength prefix2 = i -> 0 <= i < n ->
  EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,y) ->
  0 < j < n - i -> Znth (i + j) seg2 0 = Znth i seg2 0 ->
  EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,EditSwapAt y 0 j).
Proof.
  intros Ht Hseg Hmeaning Hp Hi [Hcompletion [Hinv1 Hinv2]] Hj Hsame.
  pose proof (proj1 Hinv2) as Hylen. cbn [fst snd] in Hylen; rewrite Hseg in Hylen.
  split.
  - destruct Hcompletion as [H1 H2]. split; [exact H1|].
    eapply edit_extension_swap; eauto; lia.
  - split; [exact Hinv1|]. apply edit_suffix_swap; auto; lia.
Qed.
Lemma edit_pair_swap_flat xs ys j :
  Zlength xs = Zlength ys -> 0 < j < Zlength xs -> Znth 0 ys 0 = Znth j ys 0 ->
  EditPairMatches (EditSwapAt xs 0 j) ys = EditPairMatches xs ys.
Proof. intros Hlen Hj Hsame. rewrite edit_pair_swap_left by auto. rewrite Hsame; lia. Qed.
Lemma edit_pair_swap_both xs ys j :
  Zlength xs = Zlength ys -> 0 < j < Zlength xs ->
  EditPairMatches (EditSwapAt xs 0 j) (EditSwapAt ys 0 j) = EditPairMatches xs ys.
Proof.
  intros Hlen Hj.
  rewrite (edit_pair_symmetric (EditSwapAt xs 0 j) (EditSwapAt ys 0 j)).
  rewrite edit_pair_swap_left by (rewrite ?edit_swap_length; lia).
  rewrite (edit_pair_symmetric ys (EditSwapAt xs 0 j)).
  rewrite edit_pair_swap_left by auto.
  repeat rewrite edit_swap_read by lia.
  rewrite !Z.eqb_refl, (proj2 (Z.eqb_neq 0 j) ltac:(lia)); cbn [Z.b2z].
  rewrite ?(Z.eqb_sym (Znth 0 ys 0) (Znth j xs 0)),
    ?(Z.eqb_sym (Znth j ys 0) (Znth 0 xs 0)),
    ?(Z.eqb_sym (Znth j ys 0) (Znth j xs 0)),
    ?(Z.eqb_sym (Znth 0 ys 0) (Znth 0 xs 0)). lia.
Qed.

Lemma edit_swap_front xs j :
  0 < j < Zlength xs -> Znth 0 (EditSwapAt xs 0 j) 0 = Znth j xs 0.
Proof.
  intros Hj. rewrite edit_swap_read by lia.
  rewrite (proj2 (Z.eqb_neq 0 j) ltac:(lia)), Z.eqb_refl; reflexivity.
Qed.
Lemma edit_pair_swap_right_improves xs ys j :
  Zlength xs = Zlength ys -> 0 < j < Zlength ys ->
  Znth 0 ys 0 <> Znth 0 xs 0 -> Znth j ys 0 = Znth 0 xs 0 ->
  EditPairMatches xs ys <= EditPairMatches xs (EditSwapAt ys 0 j).
Proof.
  intros Hlen Hj Hne Heq. rewrite (edit_pair_symmetric xs ys), (edit_pair_symmetric xs (EditSwapAt ys 0 j)).
  apply edit_pair_swap_improves; auto.
Qed.

(** Exchange argument: the earlier of two available positions lies in the
    other current region as well. A common first bit can therefore be chosen
    without decreasing the number of matches. The candidate set is arbitrary
    provided it is closed under the indicated, legal region transpositions. *)
Lemma edit_force_common_ordered
    (P : list Z * list Z -> Prop) r1 r2 xs ys m bit j k :
  0 < m -> Zlength xs = m -> Zlength ys = m ->
  Forall (fun x => x = 0 \/ x = 1) ys -> (bit = 0 \/ bit = 1) ->
  P (xs,ys) -> Znth 0 xs 0 = Znth 0 ys 0 -> Znth 0 ys 0 <> bit ->
  0 < j <= k -> k < m -> Znth j xs 0 = bit -> Znth k ys 0 = bit ->
  Znth j r1 0 = Znth 0 r1 0 -> Znth k r2 0 = Znth 0 r2 0 ->
  (forall a b, 0 <= a <= b -> b < m -> Znth b r2 0 = Znth 0 r2 0 -> Znth a r2 0 = Znth 0 r2 0) ->
  (forall u v q, P (u,v) -> 0 < q < m -> Znth q r1 0 = Znth 0 r1 0 -> P (EditSwapAt u 0 q,v)) ->
  (forall u v q, P (u,v) -> 0 < q < m -> Znth q r2 0 = Znth 0 r2 0 -> P (u,EditSwapAt v 0 q)) ->
  exists u v, P (u,v) /\ Znth 0 u 0 = bit /\ Znth 0 v 0 = bit /\
    EditPairMatches xs ys <= EditPairMatches u v.
Proof.
  intros Hm Hx Hy Hbinary Hbit HP Hheads Hnot Hjk Hkm Hxj Hyk Hr1 Hr2 Hclosed Hswap1 Hswap2.
  assert (Hj2 : Znth j r2 0 = Znth 0 r2 0) by (apply (Hclosed j k); auto; lia).
  pose proof (proj1 (Forall_Znth _ 0 ys) Hbinary 0 ltac:(lia)) as Hheadbit.
  pose proof (proj1 (Forall_Znth _ 0 ys) Hbinary j ltac:(lia)) as Hjbit.
  assert (Hchoice : Znth j ys 0 = bit \/ Znth j ys 0 = Znth 0 ys 0) by
    (destruct Hbit, Hheadbit, Hjbit; lia).
  destruct Hchoice as [Hcommon|Hflat].
  - exists (EditSwapAt xs 0 j), (EditSwapAt ys 0 j). split.
    + apply Hswap2; auto; try lia. apply Hswap1; auto; lia.
    + split; [rewrite edit_swap_front by lia; exact Hxj|].
      split; [rewrite edit_swap_front by lia; exact Hcommon|].
      rewrite edit_pair_swap_both by lia; lia.
  - exists (EditSwapAt xs 0 j), (EditSwapAt ys 0 k). split.
    + apply Hswap2; auto; try lia. apply Hswap1; auto; lia.
    + split; [rewrite edit_swap_front by lia; exact Hxj|].
      split; [rewrite edit_swap_front by lia; exact Hyk|].
      assert (Hsame_score : EditPairMatches (EditSwapAt xs 0 j) ys = EditPairMatches xs ys).
      { apply edit_pair_swap_flat; auto; lia. }
      rewrite <- Hsame_score. apply edit_pair_swap_right_improves; try lia; try (rewrite edit_swap_length; lia).
      * rewrite edit_swap_front by lia. rewrite Hxj; exact Hnot.
      * rewrite edit_swap_front by lia. rewrite Hxj; exact Hyk.
Qed.
Lemma edit_force_common
    (P : list Z * list Z -> Prop) r1 r2 xs ys m bit j k :
  0 < m -> Zlength xs = m -> Zlength ys = m ->
  Forall (fun x => x = 0 \/ x = 1) xs -> Forall (fun x => x = 0 \/ x = 1) ys ->
  (bit = 0 \/ bit = 1) -> P (xs,ys) ->
  0 <= j < m -> 0 <= k < m -> Znth j xs 0 = bit -> Znth k ys 0 = bit ->
  Znth j r1 0 = Znth 0 r1 0 -> Znth k r2 0 = Znth 0 r2 0 ->
  (forall a b, 0 <= a <= b -> b < m -> Znth b r1 0 = Znth 0 r1 0 -> Znth a r1 0 = Znth 0 r1 0) ->
  (forall a b, 0 <= a <= b -> b < m -> Znth b r2 0 = Znth 0 r2 0 -> Znth a r2 0 = Znth 0 r2 0) ->
  (forall u v q, P (u,v) -> 0 < q < m -> Znth q r1 0 = Znth 0 r1 0 -> P (EditSwapAt u 0 q,v)) ->
  (forall u v q, P (u,v) -> 0 < q < m -> Znth q r2 0 = Znth 0 r2 0 -> P (u,EditSwapAt v 0 q)) ->
  exists u v, P (u,v) /\ Znth 0 u 0 = bit /\ Znth 0 v 0 = bit /\
    EditPairMatches xs ys <= EditPairMatches u v.
Proof.
  intros Hm Hx Hy Hb1 Hb2 Hbit HP Hj Hk Hxj Hyk Hr1 Hr2 Hclosed1 Hclosed2 Hswap1 Hswap2.
  destruct (Z.eq_dec (Znth 0 xs 0) bit) as [Hfirst|Hfirst];
    destruct (Z.eq_dec (Znth 0 ys 0) bit) as [Hsecond|Hsecond].
  - exists xs, ys; repeat split; auto; lia.
  - assert (Hkp : 0 < k) by (destruct (Z.eq_dec k 0); subst; try contradiction; lia).
    exists xs, (EditSwapAt ys 0 k). split; [apply Hswap2; auto; lia|].
    split; [exact Hfirst|]. split; [rewrite edit_swap_front by lia; exact Hyk|].
    apply edit_pair_swap_right_improves; auto; try lia; rewrite Hfirst; assumption.
  - assert (Hjp : 0 < j) by (destruct (Z.eq_dec j 0); subst; try contradiction; lia).
    exists (EditSwapAt xs 0 j), ys. split; [apply Hswap1; auto; lia|].
    split; [rewrite edit_swap_front by lia; exact Hxj|]. split; [exact Hsecond|].
    apply edit_pair_swap_improves; auto; try lia; rewrite Hsecond; assumption.
  - assert (Hjp : 0 < j) by (destruct (Z.eq_dec j 0); subst; try contradiction; lia).
    assert (Hkp : 0 < k) by (destruct (Z.eq_dec k 0); subst; try contradiction; lia).
    pose proof (proj1 (Forall_Znth _ 0 xs) Hb1 0 ltac:(lia)) as Hhead1.
    pose proof (proj1 (Forall_Znth _ 0 ys) Hb2 0 ltac:(lia)) as Hhead2.
    assert (Hequal : Znth 0 xs 0 = Znth 0 ys 0) by (destruct Hbit, Hhead1, Hhead2; lia).
    destruct (Z_le_dec j k) as [Hjk|Hkj].
    + eapply edit_force_common_ordered with (r1 := r1) (r2 := r2) (m := m) (j := j) (k := k); eauto; lia.
    + assert (Hreverse : exists v u,
        (fun outputs : list Z * list Z => P (snd outputs, fst outputs)) (v,u) /\
        Znth 0 v 0 = bit /\ Znth 0 u 0 = bit /\ EditPairMatches ys xs <= EditPairMatches v u).
      { eapply (edit_force_common_ordered
          (fun outputs : list Z * list Z => P (snd outputs, fst outputs)) r2 r1 ys xs m bit k j);
          cbn [fst snd]; eauto; try lia; try congruence.
        all: intros u v q Hprev Hq Hlabel; cbn [fst snd] in *;
          first [apply Hswap2; auto | apply Hswap1; auto]. }
      destruct Hreverse as [v [u [HP' [Hv [Hu Hscore]]]]]. cbn [fst snd] in HP'.
      exists u, v. split; [exact HP'|]. split; [exact Hu|]. split; [exact Hv|].
      rewrite (edit_pair_symmetric xs ys), (edit_pair_symmetric u v); exact Hscore.
Qed.

Lemma edit_inventory_bounds regions values block bit :
  0 <= EditInventoryCount regions values block bit <= Zlength values.
Proof.
  revert values. induction regions as [|r regions IH]; intros values.
  - change (0 <= 0 <= Zlength values); split; [lia|apply Zlength_nonneg].
  - destruct values as [|v values]; [change (0 <= 0 <= 0); lia|].
    rewrite edit_inventory_cons, Zlength_cons. specialize (IH values).
    destruct (Z.eqb r block && Z.eqb v bit); cbn [Z.b2z]; lia.
Qed.
Lemma edit_inventory_positive regions values block bit :
  Zlength regions = Zlength values -> 0 < EditInventoryCount regions values block bit ->
  exists j, 0 <= j < Zlength values /\ Znth j regions 0 = block /\ Znth j values 0 = bit.
Proof.
  revert values. induction regions as [|r regions IH]; intros [|v values] Hlen Hpos;
    try (change (0 < 0) in Hpos; lia).
  rewrite edit_inventory_cons in Hpos.
  destruct (Z.eqb r block && Z.eqb v bit) eqn:Htest.
  - apply andb_true_iff in Htest as [Hr Hv]. apply Z.eqb_eq in Hr, Hv.
    exists 0. split; [rewrite Zlength_cons; pose proof (Zlength_nonneg values); lia|].
    cbn [Znth]; auto.
  - cbn [Z.b2z] in Hpos.
    destruct (IH values ltac:(rewrite !Zlength_cons in Hlen; lia) ltac:(lia)) as [j [Hj [Hr Hv]]].
    exists (j + 1). split; [rewrite Zlength_cons; lia|].
    rewrite !Znth_cons by lia. replace (j + 1 - 1) with j by lia; auto.
Qed.
Lemma edit_inventory_at_positive regions values j block bit :
  Zlength regions = Zlength values -> 0 <= j < Zlength values ->
  Znth j regions 0 = block -> Znth j values 0 = bit ->
  0 < EditInventoryCount regions values block bit.
Proof.
  revert values j. induction regions as [|r regions IH]; intros [|v values] j Hlen Hj Hr Hv;
    rewrite ?Zlength_cons, ?Zlength_nil in *; try lia;
    try (pose proof (Zlength_nonneg regions); lia); try (pose proof (Zlength_nonneg values); lia).
  rewrite edit_inventory_cons.
  destruct (Z.eq_dec j 0) as [->|Hne].
  - change (r = block) in Hr. change (v = bit) in Hv. subst r v.
    rewrite !Z.eqb_refl. cbn [andb Z.b2z]. pose proof (edit_inventory_bounds regions values block bit); lia.
  - rewrite Znth_cons in Hr, Hv by lia.
    pose proof (IH values (j - 1) ltac:(lia) ltac:(lia) Hr Hv) as Htail.
    destruct (Z.eqb r block && Z.eqb v bit); cbn [Z.b2z]; lia.
Qed.
Lemma edit_suffix_regions regions i :
  0 <= i < Zlength regions ->
  sublist i (Zlength regions) regions = Znth i regions 0 :: sublist (i + 1) (Zlength regions) regions.
Proof.
  intros Hi. rewrite (sublist_split i (Zlength regions) (i + 1)) by lia.
  rewrite (sublist_single 0 i regions) by lia; reflexivity.
Qed.
Lemma edit_count_tail_iff regions i counts label bit target values :
  Zlength counts = Zlength regions -> 0 <= i < Zlength regions ->
  label = Znth i regions 0 -> 0 <= label < Zlength regions ->
  (forall block, 0 <= block < Zlength regions ->
    EditInventoryCount (sublist i (Zlength regions) regions) (bit :: values) block target = Znth block counts 0) <->
  (forall block, 0 <= block < Zlength regions ->
    EditInventoryCount (sublist (i + 1) (Zlength regions) regions) values block target =
    Znth block (if Z.eqb bit target then replace_Znth label (Znth label counts 0 - 1) counts else counts) 0).
Proof.
  intros Hlen Hi Hlabel Hlabel_range.
  assert (Hpoint : forall block, 0 <= block < Zlength regions ->
    (EditInventoryCount (sublist i (Zlength regions) regions) (bit :: values) block target = Znth block counts 0 <->
     EditInventoryCount (sublist (i + 1) (Zlength regions) regions) values block target =
       Znth block (if Z.eqb bit target then replace_Znth label (Znth label counts 0 - 1) counts else counts) 0)).
  { intros block Hb. rewrite (edit_suffix_regions regions i Hi), edit_inventory_cons, <- Hlabel.
    destruct (Z.eqb bit target) eqn:Hbit.
    - rewrite andb_true_r. destruct (Z.eq_dec label block) as [->|Hne].
      + rewrite Z.eqb_refl, Znth_replace_Znth_Same by lia. cbn [Z.b2z]; lia.
      + rewrite (proj2 (Z.eqb_neq label block) Hne), Znth_replace_Znth_Diff by lia. cbn [Z.b2z]; lia.
    - rewrite andb_false_r. cbn [Z.b2z]; lia. }
  split; intros H block Hb; [apply (proj1 (Hpoint block Hb))|apply (proj2 (Hpoint block Hb))]; auto.
Qed.
Lemma edit_inventory_tail_iff regions i zeroes ones label bit values :
  Zlength zeroes = Zlength regions -> Zlength ones = Zlength regions ->
  0 <= i < Zlength regions -> label = Znth i regions 0 -> 0 <= label < Zlength regions ->
  (bit = 0 \/ bit = 1) ->
  (EditSuffixInventory regions i zeroes ones (bit :: values) <->
   EditSuffixInventory regions (i + 1)
     (if Z.eqb bit 0 then replace_Znth label (Znth label zeroes 0 - 1) zeroes else zeroes)
     (if Z.eqb bit 1 then replace_Znth label (Znth label ones 0 - 1) ones else ones) values).
Proof.
  intros Hz Ho Hi Hlabel Hrange Hbit.
  pose proof (edit_count_tail_iff regions i zeroes label bit 0 values Hz Hi Hlabel Hrange) as Hzero.
  pose proof (edit_count_tail_iff regions i ones label bit 1 values Ho Hi Hlabel Hrange) as Hone.
  split; intros [Hlen [Hbinary Hcounts]].
  - split; [rewrite Zlength_cons in Hlen; lia|]. split; [inversion Hbinary; assumption|].
    assert (Hzero' : forall b, 0 <= b < Zlength regions ->
      EditInventoryCount (sublist (i + 1) (Zlength regions) regions) values b 0 =
      Znth b (if Z.eqb bit 0 then replace_Znth label (Znth label zeroes 0 - 1) zeroes else zeroes) 0).
    { apply Hzero. intros b Hb; exact (proj1 (Hcounts b Hb)). }
    assert (Hone' : forall b, 0 <= b < Zlength regions ->
      EditInventoryCount (sublist (i + 1) (Zlength regions) regions) values b 1 =
      Znth b (if Z.eqb bit 1 then replace_Znth label (Znth label ones 0 - 1) ones else ones) 0).
    { apply Hone. intros b Hb; exact (proj2 (Hcounts b Hb)). }
    intros b Hb; split; auto.
  - split; [rewrite Zlength_cons; lia|]. split; [constructor; auto|].
    assert (Hzero' : forall b, 0 <= b < Zlength regions ->
      EditInventoryCount (sublist i (Zlength regions) regions) (bit :: values) b 0 = Znth b zeroes 0).
    { apply Hzero. intros b Hb; exact (proj1 (Hcounts b Hb)). }
    assert (Hone' : forall b, 0 <= b < Zlength regions ->
      EditInventoryCount (sublist i (Zlength regions) regions) (bit :: values) b 1 = Znth b ones 0).
    { apply Hone. intros b Hb; exact (proj2 (Hcounts b Hb)). }
    intros b Hb; split; auto.
Qed.
Lemma edit_pair_app xs ys a b :
  Zlength xs = Zlength ys ->
  EditPairMatches (xs ++ a) (ys ++ b) = EditPairMatches xs ys + EditPairMatches a b.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen;
    rewrite ?Zlength_cons, ?Zlength_nil in Hlen;
    try (pose proof (Zlength_nonneg xs); lia); try (pose proof (Zlength_nonneg ys); lia).
  - reflexivity.
  - cbn [List.app]. rewrite !edit_pair_cons, IH by lia. lia.
Qed.
Lemma edit_completion_cons s1 s2 t1 t2 prefix1 prefix2 bit1 bit2 xs ys :
  EditCompletion s1 s2 t1 t2 prefix1 prefix2 (bit1 :: xs, bit2 :: ys) <->
  EditCompletion s1 s2 t1 t2 (prefix1 ++ [bit1]) (prefix2 ++ [bit2]) (xs,ys).
Proof.
  unfold EditCompletion. cbn [fst snd]. rewrite <- !List.app_assoc. reflexivity.
Qed.

Lemma edit_region_suffix_closed t seg n i :
  Zlength seg = n -> EditSegmentMeaning t n seg -> 0 <= i < n ->
  forall j k, 0 <= j <= k -> k < n - i ->
    Znth k (sublist i n seg) 0 = Znth 0 (sublist i n seg) 0 ->
    Znth j (sublist i n seg) 0 = Znth 0 (sublist i n seg) 0.
Proof.
  intros Hlen Hmeaning Hi j k Hjk Hkn Hlabel.
  rewrite !Znth_sublist in * by lia. rewrite Z.add_0_l in *.
  eapply (edit_region_between t seg n i (j + i) (k + i)); eauto; lia.
Qed.
Lemma edit_remaining_force_common s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit answer :
  Zlength t1 = n -> Zlength t2 = n -> Zlength seg1 = n -> Zlength seg2 = n ->
  EditSegmentMeaning t1 n seg1 -> EditSegmentMeaning t2 n seg2 ->
  Zlength prefix1 = i -> Zlength prefix2 = i -> 0 <= i < n ->
  a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  (bit = 0 \/ bit = 1) ->
  0 < Znth a (if Z.eqb bit 0 then c10 else c11) 0 ->
  0 < Znth b (if Z.eqb bit 0 then c20 else c21) 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  exists xs ys,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit :: xs,bit :: ys) /\
    EditPairMatches (bit :: xs) (bit :: ys) = answer.
Proof.
  intros Ht1 Ht2 Hseg1 Hseg2 Hmeaning1 Hmeaning2 Hp1 Hp2 Hi Ha Hb Har Hbr Hbit Hpos1 Hpos2
    [[xs ys] [[HP Hupper] Hvalue]]. cbn [fst snd] in Hupper, Hvalue.
  pose proof HP as [Hcompletion [[Hx [Hbinary1 Hcounts1]] [Hy [Hbinary2 Hcounts2]]]].
  cbn [fst snd] in Hx, Hy, Hbinary1, Hbinary2, Hcounts1, Hcounts2.
  rewrite Hseg1 in Hx, Hcounts1. rewrite Hseg2 in Hy, Hcounts2.
  set (r1 := sublist i n seg1). set (r2 := sublist i n seg2).
  assert (Hrlen1 : Zlength r1 = n - i) by (unfold r1; rewrite Zlength_sublist; lia).
  assert (Hrlen2 : Zlength r2 = n - i) by (unfold r2; rewrite Zlength_sublist; lia).
  assert (Hrhead1 : Znth 0 r1 0 = a).
  { unfold r1. rewrite Znth_sublist by lia. rewrite Z.add_0_l; symmetry; exact Ha. }
  assert (Hrhead2 : Znth 0 r2 0 = b).
  { unfold r2. rewrite Znth_sublist by lia. rewrite Z.add_0_l; symmetry; exact Hb. }
  assert (Hcount1 : 0 < EditInventoryCount r1 xs a bit).
  { unfold r1. destruct Hbit as [-> | ->]; cbn [Z.eqb] in Hpos1 |- *;
      [rewrite (proj1 (Hcounts1 a Har))|rewrite (proj2 (Hcounts1 a Har))]; exact Hpos1. }
  assert (Hcount2 : 0 < EditInventoryCount r2 ys b bit).
  { unfold r2. destruct Hbit as [-> | ->]; cbn [Z.eqb] in Hpos2 |- *;
      [rewrite (proj1 (Hcounts2 b Hbr))|rewrite (proj2 (Hcounts2 b Hbr))]; exact Hpos2. }
  destruct (edit_inventory_positive r1 xs a bit ltac:(lia) Hcount1) as [j [Hj [Hjr Hjbit]]].
  destruct (edit_inventory_positive r2 ys b bit ltac:(lia) Hcount2) as [k [Hk [Hkr Hkbit]]].
  assert (Hclosed1 : forall j k, 0 <= j <= k -> k < n - i ->
    Znth k r1 0 = Znth 0 r1 0 -> Znth j r1 0 = Znth 0 r1 0).
  { apply (edit_region_suffix_closed t1 seg1 n i); auto. }
  assert (Hclosed2 : forall j k, 0 <= j <= k -> k < n - i ->
    Znth k r2 0 = Znth 0 r2 0 -> Znth j r2 0 = Znth 0 r2 0).
  { apply (edit_region_suffix_closed t2 seg2 n i); auto. }
  assert (Hswap1 : forall u v q,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,v) ->
    0 < q < n - i -> Znth q r1 0 = Znth 0 r1 0 ->
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (EditSwapAt u 0 q,v)).
  { intros u v q Hprev Hq Hlabel. unfold r1 in Hlabel.
    rewrite !Znth_sublist in Hlabel by lia. rewrite Z.add_0_l in Hlabel.
    replace (q + i) with (i + q) in Hlabel by lia.
    eapply edit_feasible_swap_left with (n := n); eauto. }
  assert (Hswap2 : forall u v q,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,v) ->
    0 < q < n - i -> Znth q r2 0 = Znth 0 r2 0 ->
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,EditSwapAt v 0 q)).
  { intros u v q Hprev Hq Hlabel. unfold r2 in Hlabel.
    rewrite !Znth_sublist in Hlabel by lia. rewrite Z.add_0_l in Hlabel.
    replace (q + i) with (i + q) in Hlabel by lia.
    eapply edit_feasible_swap_right with (n := n); eauto. }
  destruct (edit_force_common
    (EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21)
    r1 r2 xs ys (n - i) bit j k ltac:(lia) Hx Hy Hbinary1 Hbinary2 Hbit HP
    ltac:(lia) ltac:(lia) Hjbit Hkbit ltac:(congruence) ltac:(congruence)
    Hclosed1 Hclosed2 Hswap1 Hswap2) as [u [v [HPuv [Hu [Hv Hscore]]]]].
  specialize (Hupper (u,v) HPuv). cbn [fst snd] in Hupper.
  assert (Hvalue' : EditPairMatches u v = answer) by lia.
  pose proof HPuv as [_ [[Hulen _] [Hvlen _]]]. cbn [fst snd] in Hulen, Hvlen.
  rewrite Hseg1 in Hulen; rewrite Hseg2 in Hvlen.
  destruct u as [|head1 us].
  { change (0 = n - i) in Hulen. exfalso; lia. }
  destruct v as [|head2 vs].
  { change (0 = n - i) in Hvlen. exfalso; lia. }
  change (head1 = bit) in Hu. change (head2 = bit) in Hv.
  subst head1 head2. exists us, vs; auto.
Qed.
Lemma edit_suffix_head_available regions i zeroes ones label bit values :
  0 <= i < Zlength regions -> label = Znth i regions 0 -> 0 <= label < Zlength regions ->
  EditSuffixInventory regions i zeroes ones (bit :: values) ->
  (bit = 0 -> 0 < Znth label zeroes 0) /\ (bit = 1 -> 0 < Znth label ones 0).
Proof.
  intros Hi Hlabel Hr [Hlen [Hbinary Hcounts]].
  specialize (Hcounts label Hr).
  rewrite (edit_suffix_regions regions i Hi), !edit_inventory_cons, <- Hlabel, !Z.eqb_refl in Hcounts.
  cbn [andb] in Hcounts.
  pose proof (edit_inventory_bounds (sublist (i + 1) (Zlength regions) regions) values label 0) as Hzero.
  pose proof (edit_inventory_bounds (sublist (i + 1) (Zlength regions) regions) values label 1) as Hone.
  split; intros ->; cbn [Z.eqb Pos.eqb Z.b2z] in Hcounts; lia.
Qed.

Lemma edit_remaining_heads s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer :
  Zlength seg1 = n -> Zlength seg2 = n -> 0 <= i < n ->
  a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  exists bit1 bit2 xs ys,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit1 :: xs,bit2 :: ys) /\
    EditPairMatches (bit1 :: xs) (bit2 :: ys) = answer /\
    (bit1 = 0 \/ bit1 = 1) /\ (bit2 = 0 \/ bit2 = 1) /\
    (bit1 = 0 -> 0 < Znth a c10 0) /\ (bit1 = 1 -> 0 < Znth a c11 0) /\
    (bit2 = 0 -> 0 < Znth b c20 0) /\ (bit2 = 1 -> 0 < Znth b c21 0).
Proof.
  intros Hseg1 Hseg2 Hi Ha Hb Har Hbr [[u v] [[HP Hupper] Hvalue]]. cbn [fst snd] in Hvalue.
  pose proof HP as [_ [Hinv1 Hinv2]]. cbn [fst snd] in Hinv1, Hinv2.
  pose proof (proj1 Hinv1) as Hulen. pose proof (proj1 Hinv2) as Hvlen.
  rewrite Hseg1 in Hulen; rewrite Hseg2 in Hvlen.
  destruct u as [|bit1 xs]; [change (0 = n - i) in Hulen; exfalso; lia|].
  destruct v as [|bit2 ys]; [change (0 = n - i) in Hvlen; exfalso; lia|].
  pose proof (Forall_inv (proj1 (proj2 Hinv1))) as Hbit1.
  pose proof (Forall_inv (proj1 (proj2 Hinv2))) as Hbit2.
  pose proof (edit_suffix_head_available seg1 i c10 c11 a bit1 xs ltac:(lia) Ha ltac:(lia) Hinv1) as [H10 H11].
  pose proof (edit_suffix_head_available seg2 i c20 c21 b bit2 ys ltac:(lia) Hb ltac:(lia) Hinv2) as [H20 H21].
  exists bit1, bit2, xs, ys. repeat first [assumption | split].
Qed.
Lemma edit_remaining_force_zero_one s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer :
  Zlength seg1 = n -> Zlength seg2 = n -> 0 <= i < n ->
  a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  ~ (0 < Znth a c10 0 /\ 0 < Znth b c20 0) ->
  ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) -> 0 < Znth a c10 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  exists xs ys,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (0 :: xs,1 :: ys) /\
    EditPairMatches (0 :: xs) (1 :: ys) = answer.
Proof.
  intros Hseg1 Hseg2 Hi Ha Hb Har Hbr Hno0 Hno1 Hpositive Hmax.
  destruct (edit_remaining_heads s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
    Hseg1 Hseg2 Hi Ha Hb Har Hbr Hmax) as
    [bit1 [bit2 [xs [ys [HP [Hvalue [Hbit1 [Hbit2 [H10 [H11 [H20 H21]]]]]]]]]]].
  assert (Hforced : bit1 = 0 /\ bit2 = 1) by tauto.
  destruct Hforced as [-> ->]. exists xs, ys; auto.
Qed.
Lemma edit_remaining_force_one_zero s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer :
  Zlength seg1 = n -> Zlength seg2 = n -> 0 <= i < n ->
  a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) -> Znth a c10 0 <= 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  exists xs ys,
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (1 :: xs,0 :: ys) /\
    EditPairMatches (1 :: xs) (0 :: ys) = answer.
Proof.
  intros Hseg1 Hseg2 Hi Ha Hb Har Hbr Hno1 Hnonpositive Hmax.
  destruct (edit_remaining_heads s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
    Hseg1 Hseg2 Hi Ha Hb Har Hbr Hmax) as
    [bit1 [bit2 [xs [ys [HP [Hvalue [Hbit1 [Hbit2 [H10 [H11 [H20 H21]]]]]]]]]]].
  assert (Hnotzero : bit1 <> 0) by (intros H; specialize (H10 H); lia).
  assert (Hforced : bit1 = 1 /\ bit2 = 0) by tauto.
  destruct Hforced as [-> ->]. exists xs, ys; auto.
Qed.
Lemma edit_feasible_cons_iff s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit1 bit2 xs ys :
  Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n ->
  0 <= i < n -> a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  (bit1 = 0 \/ bit1 = 1) -> (bit2 = 0 \/ bit2 = 1) ->
  (EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit1 :: xs,bit2 :: ys) <->
   EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 (prefix1 ++ [bit1]) (prefix2 ++ [bit2]) (i + 1)
     (if Z.eqb bit1 0 then replace_Znth a (Znth a c10 0 - 1) c10 else c10)
     (if Z.eqb bit1 1 then replace_Znth a (Znth a c11 0 - 1) c11 else c11)
     (if Z.eqb bit2 0 then replace_Znth b (Znth b c20 0 - 1) c20 else c20)
     (if Z.eqb bit2 1 then replace_Znth b (Znth b c21 0 - 1) c21 else c21) (xs,ys)).
Proof.
  intros Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr Hbit1 Hbit2.
  unfold EditFeasibleSuffix. cbn [fst snd]. rewrite edit_completion_cons.
  rewrite (edit_inventory_tail_iff seg1 i c10 c11 a bit1 xs ltac:(lia) ltac:(lia) ltac:(lia) Ha ltac:(lia) Hbit1).
  rewrite (edit_inventory_tail_iff seg2 i c20 c21 b bit2 ys ltac:(lia) ltac:(lia) ltac:(lia) Hb ltac:(lia) Hbit2).
  reflexivity.
Qed.
Lemma edit_maximum_strip (P Q : list Z * list Z -> Prop) bit1 bit2 answer :
  max_value_of_subset Z.le P (fun outputs => EditPairMatches (fst outputs) (snd outputs)) answer ->
  (forall xs ys, P (bit1 :: xs,bit2 :: ys) <-> Q (xs,ys)) ->
  (exists xs ys, P (bit1 :: xs,bit2 :: ys) /\ EditPairMatches (bit1 :: xs) (bit2 :: ys) = answer) ->
  max_value_of_subset Z.le Q (fun outputs => EditPairMatches (fst outputs) (snd outputs))
    (answer - Z.b2z (Z.eqb bit1 bit2)).
Proof.
  intros [best [[Hbest Hupper] Hbestvalue]] Hiff [xs [ys [HP Hvalue]]].
  exists (xs,ys). split; [split|].
  - apply Hiff; exact HP.
  - intros [u v] HQ. specialize (Hupper (bit1 :: u,bit2 :: v) (proj2 (Hiff u v) HQ)).
    cbn [fst snd] in *. rewrite edit_pair_cons in Hupper, Hvalue. lia.
  - cbn [fst snd]. rewrite edit_pair_cons in Hvalue; lia.
Qed.
Lemma edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit1 bit2 answer :
  Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n ->
  0 <= i < n -> a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  (bit1 = 0 \/ bit1 = 1) -> (bit2 = 0 \/ bit2 = 1) ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  (exists xs ys, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    (bit1 :: xs,bit2 :: ys) /\ EditPairMatches (bit1 :: xs) (bit2 :: ys) = answer) ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1 ++ [bit1]) (prefix2 ++ [bit2]) (i + 1)
    (if Z.eqb bit1 0 then replace_Znth a (Znth a c10 0 - 1) c10 else c10)
    (if Z.eqb bit1 1 then replace_Znth a (Znth a c11 0 - 1) c11 else c11)
    (if Z.eqb bit2 0 then replace_Znth b (Znth b c20 0 - 1) c20 else c20)
    (if Z.eqb bit2 1 then replace_Znth b (Znth b c21 0 - 1) c21 else c21)
    (answer - Z.b2z (Z.eqb bit1 bit2)).
Proof.
  intros Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr Hbit1 Hbit2 Hmax Hforced.
  eapply edit_maximum_strip; [exact Hmax| |exact Hforced].
  intros xs ys. apply (edit_feasible_cons_iff s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b bit1 bit2 xs ys); auto.
Qed.
Lemma edit_suffix_count_bounds regions i zeroes ones values n :
  Zlength regions = n -> Zlength zeroes = n -> Zlength ones = n -> 0 <= i ->
  EditSuffixInventory regions i zeroes ones values ->
  (Forall (Z.le 0) zeroes /\ Forall (Z.ge n) zeroes) /\
  (Forall (Z.le 0) ones /\ Forall (Z.ge n) ones).
Proof.
  intros Hr Hz Ho Hi [Hlen [Hbinary Hcounts]]. rewrite Hr in Hlen, Hcounts.
  split; apply (proj2 (edit_bounds_iff _ 0 n)); intros block Hb.
  - rewrite Hz in Hb. specialize (Hcounts block Hb).
    pose proof (edit_inventory_bounds (sublist i n regions) values block 0). lia.
  - rewrite Ho in Hb. specialize (Hcounts block Hb).
    pose proof (edit_inventory_bounds (sublist i n regions) values block 1). lia.
Qed.
Lemma edit_remaining_empty s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 c10 c11 c20 c21 n answer :
  Zlength seg1 = n -> Zlength seg2 = n ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 n c10 c11 c20 c21 answer -> answer = 0.
Proof.
  intros Hseg1 Hseg2 [[xs ys] [[HP Hupper] Hvalue]].
  pose proof HP as [_ [[Hx _] [Hy _]]]. cbn [fst snd] in Hx, Hy, Hvalue.
  rewrite Hseg1, Z.sub_diag in Hx. rewrite Hseg2, Z.sub_diag in Hy.
  destruct xs as [|x xs]; [|rewrite Zlength_cons in Hx; pose proof (Zlength_nonneg xs); lia].
  destruct ys as [|y ys]; [|rewrite Zlength_cons in Hy; pose proof (Zlength_nonneg ys); lia].
  change (0 = answer) in Hvalue; symmetry; exact Hvalue.
Qed.

Lemma edit_remaining_common_step s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit answer :
  Zlength t1 = n -> Zlength t2 = n -> Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n ->
  EditSegmentMeaning t1 n seg1 -> EditSegmentMeaning t2 n seg2 ->
  Zlength prefix1 = i -> Zlength prefix2 = i -> 0 <= i < n ->
  a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  (bit = 0 \/ bit = 1) ->
  0 < Znth a (if Z.eqb bit 0 then c10 else c11) 0 ->
  0 < Znth b (if Z.eqb bit 0 then c20 else c21) 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1 ++ [bit]) (prefix2 ++ [bit]) (i + 1)
    (if Z.eqb bit 0 then replace_Znth a (Znth a c10 0 - 1) c10 else c10)
    (if Z.eqb bit 1 then replace_Znth a (Znth a c11 0 - 1) c11 else c11)
    (if Z.eqb bit 0 then replace_Znth b (Znth b c20 0 - 1) c20 else c20)
    (if Z.eqb bit 1 then replace_Znth b (Znth b c21 0 - 1) c21 else c21) (answer - 1).
Proof.
  intros Ht1 Ht2 Hseg1 Hseg2 H10 H11 H20 H21 Hmeaning1 Hmeaning2 Hp1 Hp2 Hi Ha Hb Har Hbr Hbit Hpos1 Hpos2 Hmax.
  pose proof (edit_remaining_force_common s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b bit answer Ht1 Ht2 Hseg1 Hseg2 Hmeaning1 Hmeaning2 Hp1 Hp2 Hi Ha Hb Har Hbr Hbit Hpos1 Hpos2 Hmax) as Hforced.
  pose proof (edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b bit bit answer Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr Hbit Hbit Hmax Hforced) as Hnext.
  rewrite Z.eqb_refl in Hnext. exact Hnext.
Qed.
Lemma edit_remaining_zero_one_step s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer :
  Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n ->
  0 <= i < n -> a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  ~ (0 < Znth a c10 0 /\ 0 < Znth b c20 0) ->
  ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) -> 0 < Znth a c10 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1 ++ [0]) (prefix2 ++ [1]) (i + 1)
    (replace_Znth a (Znth a c10 0 - 1) c10) c11 c20 (replace_Znth b (Znth b c21 0 - 1) c21) answer.
Proof.
  intros Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr Hno0 Hno1 Hpositive Hmax.
  pose proof (edit_remaining_force_zero_one s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b answer Hseg1 Hseg2 Hi Ha Hb Har Hbr Hno0 Hno1 Hpositive Hmax) as Hforced.
  pose proof (edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b 0 1 answer Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr ltac:(auto) ltac:(auto) Hmax Hforced) as Hnext.
  cbn [Z.eqb Pos.eqb Z.b2z] in Hnext. rewrite Z.sub_0_r in Hnext; exact Hnext.
Qed.
Lemma edit_remaining_one_zero_step s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer :
  Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n ->
  0 <= i < n -> a = Znth i seg1 0 -> b = Znth i seg2 0 -> 0 <= a < n -> 0 <= b < n ->
  ~ (0 < Znth a c11 0 /\ 0 < Znth b c21 0) -> Znth a c10 0 <= 0 ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1 ++ [1]) (prefix2 ++ [0]) (i + 1)
    c10 (replace_Znth a (Znth a c11 0 - 1) c11) (replace_Znth b (Znth b c20 0 - 1) c20) c21 answer.
Proof.
  intros Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr Hno1 Hnonpositive Hmax.
  pose proof (edit_remaining_force_one_zero s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b answer Hseg1 Hseg2 Hi Ha Hb Har Hbr Hno1 Hnonpositive Hmax) as Hforced.
  pose proof (edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21
    n a b 1 0 answer Hseg1 Hseg2 H10 H11 H20 H21 Hi Ha Hb Har Hbr ltac:(auto) ltac:(auto) Hmax Hforced) as Hnext.
  cbn [Z.eqb Pos.eqb Z.b2z] in Hnext. rewrite Z.sub_0_r in Hnext; exact Hnext.
Qed.
Lemma edit_remaining_count_bounds s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n answer :
  Zlength seg1 = n -> Zlength seg2 = n ->
  Zlength c10 = n -> Zlength c11 = n -> Zlength c20 = n -> Zlength c21 = n -> 0 <= i ->
  EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer ->
  (Forall (Z.le 0) c10 /\ Forall (Z.ge n) c10) /\
  (Forall (Z.le 0) c11 /\ Forall (Z.ge n) c11) /\
  (Forall (Z.le 0) c20 /\ Forall (Z.ge n) c20) /\
  (Forall (Z.le 0) c21 /\ Forall (Z.ge n) c21).
Proof.
  intros Hseg1 Hseg2 H10 H11 H20 H21 Hi [[xs ys] [[HP Hupper] Hvalue]].
  destruct HP as [_ [Hinv1 Hinv2]]. cbn [fst snd] in Hinv1, Hinv2.
  pose proof (edit_suffix_count_bounds seg1 i c10 c11 xs n Hseg1 H10 H11 Hi Hinv1) as [HC10 HC11].
  pose proof (edit_suffix_count_bounds seg2 i c20 c21 ys n Hseg2 H20 H21 Hi Hinv2) as [HC20 HC21].
  auto.
Qed.

Lemma edit_zero_read xs i : Forall (eq 0) xs -> Znth i xs 0 = 0.
Proof.
  intros H. unfold Znth. generalize (Z.to_nat i) as k.
  induction H; intros [|k]; cbn; auto.
Qed.
Lemma edit_bounded_read xs i lo hi :
  Forall (Z.le lo) xs -> Forall (Z.ge hi) xs -> lo <= 0 <= hi -> lo <= Znth i xs 0 <= hi.
Proof.
  intros Hlo Hhi Hzero. unfold Znth.
  destruct (lt_dec (Z.to_nat i) (length xs)) as [Hin|Hout].
  - assert (Hmember : In (nth (Z.to_nat i) xs 0) xs) by (apply nth_In; exact Hin).
    rewrite Forall_forall in Hlo, Hhi. specialize (Hlo _ Hmember). specialize (Hhi _ Hmember). lia.
  - rewrite nth_overflow by lia; exact Hzero.
Qed.

(** The build-phase proofs reuse the original counting and region lemmas. *)
Lemma edit_counts_bounds s t n upto zeroes ones :
  0 <= n -> Zlength s = n -> Zlength zeroes = n -> Zlength ones = n ->
  EditCountsMeaning s t n upto zeroes ones ->
  (Forall (Z.le 0) zeroes /\ Forall (Z.ge n) zeroes) /\
  (Forall (Z.le 0) ones /\ Forall (Z.ge n) ones).
Proof.
  intros Hn Hs Hz Ho [HC0 HC1]. split; apply (proj2 (edit_bounds_iff _ 0 n)); intros b Hb.
  - rewrite Hz in Hb. rewrite (HC0 b Hb), <- edit_block_bit_count_eq.
    apply edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts; auto.
  - rewrite Ho in Hb. rewrite (HC1 b Hb), <- edit_block_bit_count_eq.
    apply edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts; auto.
Qed.
Lemma edit_zero_bounds xs n :
  0 <= n -> Forall (eq 0) xs -> Forall (Z.le 0) xs /\ Forall (Z.ge n) xs.
Proof.
  intros Hn Hzero. split; eapply Forall_impl; [|exact Hzero| |exact Hzero]; intros x Hx; subst x; lia.
Qed.
Lemma edit_build_first_zero s t n zeroes ones :
  1 <= n -> Zlength s = n -> Zlength zeroes = n -> Zlength ones = n ->
  Forall (eq 0) zeroes -> Forall (eq 0) ones -> Znth 0 s 0 = 0 ->
  EditBuildMeaning s t n 1 [0] (replace_Znth 0 (Znth 0 zeroes 0 + 1) zeroes) ones.
Proof.
  intros Hn Hs Hz Ho Hzero Hone Hbit. split.
  - intros idx Hi. assert (idx = 0) by lia. subst idx.
    change (EditBlockStart t 0 0). split; [lia|]. split; [intros k Hk; lia|left; reflexivity].
  - pose proof (EditCountsForPrefix_initial_zero__zeroing_and_base_build s t n zeroes ones Hn Hs Hbit
      (proj2 (edit_zero_full_iff n zeroes) (conj Hz Hzero))
      (proj2 (edit_zero_full_iff n ones) (conj Ho Hone))) as Hcounts.
    apply edit_counts_iff in Hcounts; exact (proj2 (proj2 Hcounts)).
Qed.
Lemma edit_build_first_one s t n zeroes ones :
  1 <= n -> Zlength s = n -> Zlength zeroes = n -> Zlength ones = n ->
  Forall (eq 0) zeroes -> Forall (eq 0) ones ->
  Forall (Z.le 0) s -> Forall (Z.ge 1) s -> Znth 0 s 0 <> 0 ->
  EditBuildMeaning s t n 1 [0] zeroes (replace_Znth 0 (Znth 0 ones 0 + 1) ones).
Proof.
  intros Hn Hs Hz Ho Hzero Hone Hlo Hhi Hbit. split.
  - intros idx Hi. assert (idx = 0) by lia. subst idx.
    change (EditBlockStart t 0 0). split; [lia|]. split; [intros k Hk; lia|left; reflexivity].
  - pose proof (EditCountsForPrefix_initial_one__zeroing_and_base_build s t n zeroes ones Hn Hs
      ltac:(intros idx Hi; eapply edit_bounded_read; eauto; lia) Hbit
      (proj2 (edit_zero_full_iff n zeroes) (conj Hz Hzero))
      (proj2 (edit_zero_full_iff n ones) (conj Ho Hone))) as Hcounts.
    apply edit_counts_iff in Hcounts; exact (proj2 (proj2 Hcounts)).
Qed.
Lemma edit_counts_inc_zero s t n i seg zeroes ones block :
  Zlength s = n -> Zlength zeroes = n -> Zlength ones = n -> Zlength seg = i + 1 ->
  0 <= i < n -> EditSegmentMeaning t (i + 1) seg -> EditCountsMeaning s t n i zeroes ones ->
  block = Znth i seg 0 -> Znth i s 0 = 0 ->
  EditCountsMeaning s t n (i + 1) (replace_Znth block (Znth block zeroes 0 + 1) zeroes) ones.
Proof.
  intros Hs Hz Ho Hseg Hi Hmeaning Hcounts Hblock Hbit.
  pose proof (edit_counts_prefix_extend_zero__build_s2_segments_counts s t n i seg zeroes ones block Hs Hi
    (proj2 (edit_segment_iff t (i + 1) seg) (conj Hseg Hmeaning))
    (proj2 (edit_counts_iff s t n i zeroes ones) (conj Hz (conj Ho Hcounts))) Hblock Hbit) as H.
  apply edit_counts_iff in H; exact (proj2 (proj2 H)).
Qed.
Lemma edit_counts_inc_one s t n i seg zeroes ones block :
  Zlength s = n -> Zlength zeroes = n -> Zlength ones = n -> Zlength seg = i + 1 ->
  0 <= i < n -> EditSegmentMeaning t (i + 1) seg -> EditCountsMeaning s t n i zeroes ones ->
  block = Znth i seg 0 -> Znth i s 0 = 1 ->
  EditCountsMeaning s t n (i + 1) zeroes (replace_Znth block (Znth block ones 0 + 1) ones).
Proof.
  intros Hs Hz Ho Hseg Hi Hmeaning Hcounts Hblock Hbit.
  pose proof (edit_counts_prefix_extend_one__build_s2_segments_counts s t n i seg zeroes ones block Hs Hi
    (proj2 (edit_segment_iff t (i + 1) seg) (conj Hseg Hmeaning))
    (proj2 (edit_counts_iff s t n i zeroes ones) (conj Hz (conj Ho Hcounts))) Hblock Hbit) as H.
  apply edit_counts_iff in H; exact (proj2 (proj2 H)).
Qed.
Lemma edit_segment_extend_same t seg i :
  Zlength seg = i -> 1 <= i -> EditSegmentMeaning t i seg -> edit_edge_open t i ->
  EditSegmentMeaning t (i + 1) (seg ++ [Znth (i - 1) seg 0]).
Proof.
  intros Hlen Hi Hmeaning Hedge.
  pose proof (edit_segment_prefix_append_same__build_s2_segments_counts t i seg
    (proj2 (edit_segment_iff t i seg) (conj Hlen Hmeaning)) Hi Hedge) as H.
  apply edit_segment_iff in H; exact (proj2 H).
Qed.
Lemma edit_segment_extend_new t seg i :
  Zlength seg = i -> 0 <= i -> EditSegmentMeaning t i seg -> ~ edit_edge_open t i ->
  EditSegmentMeaning t (i + 1) (seg ++ [i]).
Proof.
  intros Hlen Hi Hmeaning Hedge.
  pose proof (edit_segment_prefix_append_new__build_s2_segments_counts t i seg
    (proj2 (edit_segment_iff t i seg) (conj Hlen Hmeaning)) Hi Hedge) as H.
  apply edit_segment_iff in H; exact (proj2 H).
Qed.
Lemma edit_segment_bound t seg upto idx :
  EditSegmentMeaning t upto seg -> 0 <= idx < upto -> 0 <= Znth idx seg 0 <= idx.
Proof. intros H Hi. exact (proj1 (H idx Hi)). Qed.
