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
