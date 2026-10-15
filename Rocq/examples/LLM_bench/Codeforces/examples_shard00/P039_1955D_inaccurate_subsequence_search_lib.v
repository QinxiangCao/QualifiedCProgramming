Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition GoodWindow (b window : list Z) (k : Z) : Prop :=
  exists rearranged,
    Permutation window rearranged /\ Zlength rearranged = Zlength b /\
    #(fun i : Z => 0 <= i < Zlength b /\
      Znth i rearranged 0 = Znth i b 0) >= k.

Definition Pre (k : Z) (a b : list Z) : Prop :=
  1 <= k <= Zlength b /\ Zlength b <= Zlength a /\ Zlength a <= 200000 /\
  Forall (fun x => 1 <= x <= 1000000) a /\ Forall (fun x => 1 <= x <= 1000000) b.

Definition Spec (k : Z) (a b : list Z) (out : Z) : Prop :=
  out = #(fun l : Z =>
    0 <= l < Zlength a - Zlength b + 1 /\
    GoodWindow b (sublist l (l + Zlength b) a) k).

(* Implementation-facing mathematical states.  These declarations are
   intentionally phrased in terms of multisets and finite prefixes rather
   than as an execution model of the C loops. *)
Definition z_min (x y : Z) : Z := Z.min x y.

Definition Occurrences (xs : list Z) (value : Z) : Z :=
  #(fun i : Z =>
      0 <= i < Zlength xs /\ Znth i xs 0 = value).

Definition FrequencyTable (xs table : list Z) : Prop :=
  Zlength table = 1000001 /\
  forall value, 0 <= value < 1000001 ->
    Znth value table 0 = Occurrences xs value.

Definition TableMatchScore
    (need_table have_table : list Z) (score : Z) : Prop :=
  score = SumLib.Sum.sum
    (fun value : Z => 0 <= value < 1000001)
    (fun value =>
       Z.min (Znth value need_table 0) (Znth value have_table 0)).

Definition CountedGoodWindows
    (k : Z) (values b : list Z) (upto answer : Z) : Prop :=
  answer = #(fun start : Z =>
    0 <= start < upto /\
    GoodWindow b
      (sublist start (start + Zlength b) values) k).

Definition ClearedByPrefix
    (original source : list Z) (upto : Z) (table : list Z) : Prop :=
  Zlength table = 1000001 /\
  (forall value,
     0 <= value < 1000001 ->
     (forall i, 0 <= i < upto -> Znth i source 0 <> value) ->
     Znth value table 0 = Znth value original 0) /\
  (forall i, 0 <= i < upto ->
     Znth (Znth i source 0) table 0 = 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma set_card_Z_as_sum__initial_safety :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_range_bounds__initial_safety :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    0 <= #(fun x : Z => low <= x < high /\ P x) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum__initial_safety.
  pose proof (SumLib.ZRange.sum_Z_range_bounds low high
    (fun x => if prop_dec (P x) then 1 else 0) 0 1 Hrange) as Hbounds.
  assert (Hpoint : forall x, low <= x < high ->
    0 <= (if prop_dec (P x) then 1 else 0) <= 1).
  { intros x Hx. destruct (prop_dec (P x)); lia. }
  specialize (Hbounds Hpoint). nia.
Qed.
Lemma occurrences_bounds__initial_safety :
  forall (xs : list Z) (value : Z),
    0 <= Occurrences xs value <= Zlength xs.
Proof.
  intros xs value.
  unfold Occurrences.
  pose proof (set_card_Z_range_bounds__initial_safety
    0 (Zlength xs) (fun i => Znth i xs 0 = value) (Zlength_nonneg xs)).
  lia.
Qed.
Lemma frequency_table_entry_bounds__initial_safety :
  forall (xs table : list Z) (value : Z),
    FrequencyTable xs table ->
    0 <= value < 1000001 ->
    0 <= Znth value table 0 <= Zlength xs.
Proof.
  intros xs table value Htable Hvalue.
  unfold FrequencyTable in Htable.
  destruct Htable as [_ Hlookup].
  rewrite Hlookup by exact Hvalue.
  apply occurrences_bounds__initial_safety.
Qed.
Lemma z_min_increment_bounds__initial_safety :
  forall x y : Z,
    Z.min x y <= Z.min (x + 1) y <= Z.min x y + 1.
Proof.
  intros x y.
  destruct (Z_le_dec x y) as [Hxy | Hxy].
  - rewrite Z.min_l by lia.
    destruct (Z_le_dec (x + 1) y) as [Hstep | Hstep].
    + rewrite Z.min_l by lia. lia.
    + rewrite Z.min_r by lia. lia.
  - rewrite Z.min_r by lia.
    rewrite Z.min_r by lia.
    lia.
Qed.
Lemma occurrences_as_range_sum__sliding_remove_safety :
  forall xs value,
    Occurrences xs value =
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength xs)
      (fun i => if prop_dec (Znth i xs 0 = value) then 1 else 0).
Proof.
  intros xs value.
  unfold Occurrences, set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter
        (fun i =>
          if prop_dec (Znth i xs 0 = value) then true else false) zs) =
    fold_right
      (fun i acc : Z =>
        (if prop_dec (Znth i xs 0 = value) then 1 else 0) + acc)
      0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (Znth z xs 0 = value)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma occurrences_bounds__sliding_remove_safety :
  forall xs value,
    0 <= Occurrences xs value <= Zlength xs.
Proof.
  intros xs value.
  rewrite occurrences_as_range_sum__sliding_remove_safety.
  pose proof
    (SumLib.ZRange.sum_Z_range_bounds 0 (Zlength xs)
      (fun i => if prop_dec (Znth i xs 0 = value) then 1 else 0)
      0 1) as Hbounds.
  specialize (Hbounds (Zlength_nonneg xs)).
  assert (Hpoint : forall i, 0 <= i < Zlength xs ->
    0 <= (if prop_dec (Znth i xs 0 = value) then 1 else 0) <= 1).
  {
    intros i Hi.
    destruct (prop_dec (Znth i xs 0 = value)); simpl; lia.
  }
  specialize (Hbounds Hpoint).
  nia.
Qed.
Lemma occurrences_present__sliding_remove_safety :
  forall xs value j,
    0 <= j < Zlength xs ->
    Znth j xs 0 = value ->
    1 <= Occurrences xs value.
Proof.
  intros xs value j Hj Hvalue.
  rewrite occurrences_as_range_sum__sliding_remove_safety.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 j (Zlength xs)) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split j (j + 1) (Zlength xs)) by lia.
  rewrite SumLib.ZRange.sum_Z_range_single.
  assert (Hnonneg : forall x,
    0 <= (if prop_dec (Znth x xs 0 = value) then 1 else 0)).
  {
    intros x.
    destruct (prop_dec (Znth x xs 0 = value)); simpl; lia.
  }
  pose proof
    (SumLib.ZRange.sum_Z_range_lower_bound 0 j
      (fun i => if prop_dec (Znth i xs 0 = value) then 1 else 0) 0
      ltac:(lia)
      ltac:(intros x Hx; apply Hnonneg))
    as Hleft.
  pose proof
    (SumLib.ZRange.sum_Z_range_lower_bound (j + 1) (Zlength xs)
      (fun i => if prop_dec (Znth i xs 0 = value) then 1 else 0) 0
      ltac:(lia)
      ltac:(intros x Hx; apply Hnonneg))
    as Hright.
  destruct (prop_dec (Znth j xs 0 = value)); [lia | contradiction].
Qed.
Lemma frequency_table_entry_bounds__sliding_remove_safety :
  forall xs table value,
    FrequencyTable xs table ->
    0 <= value < 1000001 ->
    0 <= Znth value table 0 <= Zlength xs.
Proof.
  intros xs table value [_ Htable] Hvalue.
  rewrite Htable by exact Hvalue.
  apply occurrences_bounds__sliding_remove_safety.
Qed.
Lemma frequency_table_present__sliding_remove_safety :
  forall xs table value j,
    FrequencyTable xs table ->
    0 <= value < 1000001 ->
    0 <= j < Zlength xs ->
    Znth j xs 0 = value ->
    1 <= Znth value table 0.
Proof.
  intros xs table value j [_ Htable] Hvalue Hj Hnth.
  rewrite Htable by exact Hvalue.
  eapply occurrences_present__sliding_remove_safety; eauto.
Qed.
Lemma set_card_Z_as_sum__sliding_add_safety :
  forall (low high : Z) (P : Z -> Prop),
    set_card (fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_range_bounds__sliding_add_safety :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    0 <= set_card (fun x : Z => low <= x < high /\ P x) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum__sliding_add_safety.
  pose proof (SumLib.ZRange.sum_Z_range_bounds low high
    (fun x => if prop_dec (P x) then 1 else 0) 0 1 Hrange) as Hbounds.
  assert (Hpoint : forall x, low <= x < high ->
    0 <= (if prop_dec (P x) then 1 else 0) <= 1).
  { intros x Hx. destruct (prop_dec (P x)); lia. }
  specialize (Hbounds Hpoint). nia.
Qed.
Lemma occurrences_bounds__sliding_add_safety :
  forall (xs : list Z) value,
    0 <= Occurrences xs value <= Zlength xs.
Proof.
  intros xs value.
  unfold Occurrences.
  pose proof (Zlength_nonneg xs).
  pose proof (set_card_Z_range_bounds__sliding_add_safety
    0 (Zlength xs) (fun i => Znth i xs 0 = value) ltac:(lia)).
  lia.
Qed.
Lemma frequency_table_entry_bounds__sliding_add_safety :
  forall (xs table : list Z) value,
    FrequencyTable xs table ->
    0 <= value < 1000001 ->
    0 <= Znth value table 0 <= Zlength xs.
Proof.
  intros xs table value [_ Htable] Hvalue.
  rewrite Htable by exact Hvalue.
  apply occurrences_bounds__sliding_add_safety.
Qed.
Lemma z_min_bounds__sliding_add_safety :
  forall x y lo hi,
    lo <= x <= hi -> lo <= y <= hi ->
    lo <= z_min x y <= hi.
Proof.
  intros x y lo hi Hx Hy.
  unfold z_min.
  destruct (Z.min_spec x y) as [[Hxy Heq] | [Hxy Heq]]; rewrite Heq; lia.
Qed.
Lemma replace_decrement_lookup_bounds__sliding_add_safety :
  forall (table : list Z) x y hi,
    Zlength table = 1000001 ->
    0 <= x < 1000001 ->
    0 <= y < 1000001 ->
    0 <= Znth y table 0 <= hi ->
    -1 <= Znth y (replace_Znth x (Znth x table 0 - 1) table) 0 <= hi.
Proof.
  intros table x y hi Hlen Hx Hy Hbound.
  destruct (Z.eq_dec x y) as [Heq | Hneq].
  - subst x.
    rewrite Znth_replace_Znth_Same by lia.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    lia.
Qed.
Lemma set_card_empty__table_initialization :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma set_card_iff__table_initialization :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros z.
      rewrite <- (@enum_ok A P FP z), <- (@enum_ok A Q FQ z).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__table_initialization :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__table_initialization :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__table_initialization.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__table_initialization :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__table_initialization.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma occurrences_prefix_succ_eq__table_initialization :
  forall (xs : list Z) i value,
    0 <= i < Zlength xs ->
    Znth i xs 0 = value ->
    Occurrences (sublist 0 (i + 1) xs) value =
      Occurrences (sublist 0 i xs) value + 1.
Proof.
  intros xs i value Hi Heq.
  unfold Occurrences.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\
      Znth z (sublist 0 (i + 1) xs) 0 = value) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z xs 0 = value)).
  {
    apply set_card_iff__table_initialization.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i xs) 0 = value) =
    #(fun z : Z => 0 <= z < i /\ Znth z xs 0 = value)).
  {
    apply set_card_iff__table_initialization.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_true__table_initialization; [lia | exact Heq].
Qed.
Lemma occurrences_prefix_succ_neq__table_initialization :
  forall (xs : list Z) i value,
    0 <= i < Zlength xs ->
    Znth i xs 0 <> value ->
    Occurrences (sublist 0 (i + 1) xs) value =
      Occurrences (sublist 0 i xs) value.
Proof.
  intros xs i value Hi Hneq.
  unfold Occurrences.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\
      Znth z (sublist 0 (i + 1) xs) 0 = value) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z xs 0 = value)).
  {
    apply set_card_iff__table_initialization.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i xs) 0 = value) =
    #(fun z : Z => 0 <= z < i /\ Znth z xs 0 = value)).
  {
    apply set_card_iff__table_initialization.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_false__table_initialization; [lia | exact Hneq].
Qed.
Lemma frequency_table_empty__table_initialization :
  forall xs,
    FrequencyTable (sublist 0 0 xs) (repeat 0 (Z.to_nat 1000001)).
Proof.
  intros xs.
  unfold FrequencyTable.
  split.
  - rewrite Zlength_correct, repeat_length.
    lia.
  - intros value Hvalue.
    rewrite Znth_repeat.
    unfold Occurrences.
    symmetry.
    apply set_card_empty__table_initialization.
    intros z [Hz _].
    rewrite Zlength_sublist0 in Hz by
      (pose proof (Zlength_nonneg xs); lia).
    lia.
Qed.
Lemma Zlength_replace_Znth__table_initialization :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  assert (Hlen : forall m (l0 : list A),
    length (replace_nth m l0 v) = length l0).
  {
    intros m; induction m; intros [|x l0]; simpl; auto.
  }
  rewrite Hlen.
  reflexivity.
Qed.
Lemma frequency_table_prefix_step__table_initialization :
  forall xs table i,
    0 <= i < Zlength xs ->
    0 <= Znth i xs 0 < 1000001 ->
    FrequencyTable (sublist 0 i xs) table ->
    FrequencyTable (sublist 0 (i + 1) xs)
      (replace_Znth (Znth i xs 0) (Znth (Znth i xs 0) table 0 + 1) table).
Proof.
  intros xs table i Hi Hitem [Hlen Htable].
  unfold FrequencyTable.
  split.
  - rewrite Zlength_replace_Znth__table_initialization. exact Hlen.
  - intros value Hvalue.
    destruct (Z.eq_dec value (Znth i xs 0)) as [Heq | Hneq].
    + subst value.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Htable by lia.
      symmetry.
      apply occurrences_prefix_succ_eq__table_initialization; auto.
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Htable by exact Hvalue.
      symmetry.
      apply occurrences_prefix_succ_neq__table_initialization; auto.
Qed.
Lemma table_match_score_zero__table_initialization :
  forall xs need_table,
    FrequencyTable xs need_table ->
    TableMatchScore need_table (repeat 0 (Z.to_nat 1000001)) 0.
Proof.
  intros xs need_table [Hlen Htable].
  unfold TableMatchScore.
  rewrite (SumLib.Sum.sum_ext
    (fun value : Z => 0 <= value < 1000001)
    (fun value => Z.min (Znth value need_table 0)
      (Znth value (repeat 0 (Z.to_nat 1000001)) 0))
    (fun _ => 0)).
  - symmetry. apply SumLib.Sum.sum_zero.
  - intros value Hvalue.
    rewrite Znth_repeat.
    rewrite Z.min_r; [reflexivity |].
    rewrite Htable by exact Hvalue.
    unfold Occurrences, set_card.
    apply SumLib.Sum.sum_nonneg.
    intros. lia.
Qed.
Lemma set_card_Z_as_sum__window_semantics :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__window_semantics :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__window_semantics.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__window_semantics :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__window_semantics.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [contradiction | lia].
Qed.
Lemma set_card_Z_iff__window_semantics :
  forall (P Q : Z -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall z, P z <-> Q z) ->
    @set_card Z P FP = @set_card Z Q FQ.
Proof.
  intros P Q FP FQ Heq.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum Z P FP) (@enum Z Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup Z P FP).
    - exact (@enum_nodup Z Q FQ).
    - intro z. rewrite <- !enum_ok. apply Heq.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma occurrences_count_occ__window_semantics :
  forall xs value,
    Occurrences xs value = Z.of_nat (count_occ Z.eq_dec xs value).
Proof.
  intros xs value.
  unfold Occurrences.
  rewrite set_card_Z_as_sum__window_semantics.
  induction xs as [|x xs IH].
  - rewrite SumLib.ZRange.sum_Z_range_empty by (rewrite Zlength_nil; lia).
    reflexivity.
  - rewrite (SumLib.ZRange.sum_Z_range_Znth_cons 0 x xs
      (fun y => if prop_dec (y = value) then 1 else 0)).
    rewrite IH. simpl count_occ.
    destruct (Z.eq_dec x value) as [Heq | Hneq].
    + destruct (prop_dec (x = value)) as [_ | Hbad]; [lia | contradiction].
    + destruct (prop_dec (x = value)) as [Hbad | _]; [contradiction | lia].
Qed.
Lemma occurrences_nonneg__window_semantics :
  forall xs value, 0 <= Occurrences xs value.
Proof.
  intros xs value. rewrite occurrences_count_occ__window_semantics. lia.
Qed.
Lemma occurrences_cons__window_semantics :
  forall x xs value,
    Occurrences (x :: xs) value =
    Occurrences xs value + (if Z.eq_dec x value then 1 else 0).
Proof.
  intros x xs value. rewrite !occurrences_count_occ__window_semantics.
  simpl count_occ. destruct (Z.eq_dec x value); lia.
Qed.
Lemma occurrences_app_single__window_semantics :
  forall xs x value,
    Occurrences (xs ++ x :: nil) value =
    Occurrences xs value + (if Z.eq_dec x value then 1 else 0).
Proof.
  intros xs x value. rewrite !occurrences_count_occ__window_semantics.
  rewrite count_occ_app. simpl count_occ.
  destruct (Z.eq_dec x value); lia.
Qed.
Lemma sum_replace_Znth_min__window_semantics :
  forall need have idx new_value,
    Zlength have = 1000001 ->
    0 <= idx < 1000001 ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Znth value need 0)
        (Znth value (replace_Znth idx new_value have) 0)) =
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Znth value need 0) (Znth value have 0)) -
      Z.min (Znth idx need 0) (Znth idx have 0) +
      Z.min (Znth idx need 0) new_value.
Proof.
  intros need have idx new_value Hlen Hidx.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 idx 1000001
    (fun value => Z.min (Znth value need 0)
      (Znth value (replace_Znth idx new_value have) 0))) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 idx 1000001
    (fun value => Z.min (Znth value need 0) (Znth value have 0))) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split idx (idx + 1) 1000001
    (fun value => Z.min (Znth value need 0)
      (Znth value (replace_Znth idx new_value have) 0))) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split idx (idx + 1) 1000001
    (fun value => Z.min (Znth value need 0) (Znth value have 0))) by lia.
  rewrite !SumLib.ZRange.sum_Z_range_single.
  rewrite Znth_replace_Znth_Same by lia.
  assert (Hprefix :
    SumLib.Sum.sum (fun value : Z => 0 <= value < idx)
      (fun value => Z.min (Znth value need 0)
        (Znth value (replace_Znth idx new_value have) 0)) =
    SumLib.Sum.sum (fun value : Z => 0 <= value < idx)
      (fun value => Z.min (Znth value need 0) (Znth value have 0))).
  {
    apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  assert (Hsuffix :
    SumLib.Sum.sum (fun value : Z => idx + 1 <= value < 1000001)
      (fun value => Z.min (Znth value need 0)
        (Znth value (replace_Znth idx new_value have) 0)) =
    SumLib.Sum.sum (fun value : Z => idx + 1 <= value < 1000001)
      (fun value => Z.min (Znth value need 0) (Znth value have 0))).
  {
    apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  rewrite Hprefix, Hsuffix. ring.
Qed.
Lemma table_match_score_update__window_semantics :
  forall need have idx new_value old_score,
    Zlength have = 1000001 ->
    0 <= idx < 1000001 ->
    TableMatchScore need have old_score ->
    TableMatchScore need (replace_Znth idx new_value have)
      (old_score - Z.min (Znth idx have 0) (Znth idx need 0) +
       Z.min new_value (Znth idx need 0)).
Proof.
  intros need have idx new_value old_score Hlen Hidx Hscore.
  unfold TableMatchScore in *. subst old_score.
  rewrite sum_replace_Znth_min__window_semantics by assumption.
  rewrite (Z.min_comm (Znth idx have 0)), (Z.min_comm new_value).
  reflexivity.
Qed.
Lemma Zlength_replace_Znth__window_semantics :
  forall {A : Type} (xs : list A) idx value,
    Zlength (replace_Znth idx value xs) = Zlength xs.
Proof.
  intros A xs idx value.
  assert (Hlength : forall (n : nat) (ys : list A) (v : A),
    length (replace_nth n ys v) = length ys).
  {
    intros n ys. revert n.
    induction ys as [|y ys IH]; intros [|n] v; simpl; auto.
  }
  unfold replace_Znth. rewrite !Zlength_correct, Hlength. reflexivity.
Qed.
Lemma table_match_score_updates__window_semantics :
  forall need have out_idx in_idx removed_value added_value score,
    Zlength have = 1000001 ->
    0 <= out_idx < 1000001 ->
    0 <= in_idx < 1000001 ->
    TableMatchScore need have score ->
    TableMatchScore need
      (replace_Znth in_idx added_value
        (replace_Znth out_idx removed_value have))
      (score - Z.min (Znth out_idx have 0) (Znth out_idx need 0) +
       Z.min removed_value (Znth out_idx need 0) -
       Z.min (Znth in_idx (replace_Znth out_idx removed_value have) 0)
         (Znth in_idx need 0) +
       Z.min added_value (Znth in_idx need 0)).
Proof.
  intros need have out_idx in_idx removed_value added_value score
    Hlen Hout Hin Hscore.
  pose proof (table_match_score_update__window_semantics
    need have out_idx removed_value score Hlen Hout Hscore) as Hremoved.
  pose proof (table_match_score_update__window_semantics
    need (replace_Znth out_idx removed_value have) in_idx added_value
    (score - Z.min (Znth out_idx have 0) (Znth out_idx need 0) +
      Z.min removed_value (Znth out_idx need 0))
    (eq_trans (Zlength_replace_Znth__window_semantics have out_idx removed_value) Hlen)
    Hin Hremoved) as Hadd.
  replace
    (score - Z.min (Znth out_idx have 0) (Znth out_idx need 0) +
       Z.min removed_value (Znth out_idx need 0) -
       Z.min (Znth in_idx (replace_Znth out_idx removed_value have) 0)
         (Znth in_idx need 0) +
       Z.min added_value (Znth in_idx need 0))
    with
    ((score - Z.min (Znth out_idx have 0) (Znth out_idx need 0) +
       Z.min removed_value (Znth out_idx need 0)) -
       Z.min (Znth in_idx (replace_Znth out_idx removed_value have) 0)
         (Znth in_idx need 0) +
       Z.min added_value (Znth in_idx need 0)) by ring.
  exact Hadd.
Qed.
Lemma table_match_score_updates_zmin__window_semantics :
  forall need have out_idx in_idx removed_value added_value score
    retval retval2 retval3 retval4,
    Zlength have = 1000001 ->
    0 <= out_idx < 1000001 ->
    0 <= in_idx < 1000001 ->
    retval = z_min (Znth out_idx have 0) (Znth out_idx need 0) ->
    retval2 = z_min removed_value (Znth out_idx need 0) ->
    retval3 = z_min (Znth in_idx (replace_Znth out_idx removed_value have) 0)
      (Znth in_idx need 0) ->
    retval4 = z_min added_value (Znth in_idx need 0) ->
    TableMatchScore need have score ->
    TableMatchScore need
      (replace_Znth in_idx added_value
        (replace_Znth out_idx removed_value have))
      (((score - retval) + retval2) - retval3 + retval4).
Proof.
  intros need have out_idx in_idx removed_value added_value score
    retval retval2 retval3 retval4 Hlen Hout Hin Hr Hr2 Hr3 Hr4 Hscore.
  unfold z_min in Hr, Hr2, Hr3, Hr4.
  pose proof (table_match_score_updates__window_semantics need have out_idx
    in_idx removed_value added_value score Hlen Hout Hin Hscore) as H.
  rewrite <- Hr, <- Hr2, <- Hr3, <- Hr4 in H. exact H.
Qed.
Lemma sublist_prefix_snoc__window_semantics :
  forall xs i,
    0 <= i < Zlength xs ->
    sublist 0 (i + 1) xs = sublist 0 i xs ++ Znth i xs 0 :: nil.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  reflexivity.
Qed.
Lemma frequency_table_app_single__window_semantics :
  forall xs table x,
    0 <= x < 1000001 ->
    FrequencyTable xs table ->
    FrequencyTable (xs ++ x :: nil)
      (replace_Znth x (Znth x table 0 + 1) table).
Proof.
  intros xs table x Hx [Hlen Htable]. split.
  - rewrite Zlength_replace_Znth__window_semantics. exact Hlen.
  - intros value Hvalue.
    rewrite occurrences_app_single__window_semantics.
    destruct (Z.eq_dec x value) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      rewrite Htable by lia. destruct (Z.eq_dec value value); [lia | contradiction].
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Htable by lia. destruct (Z.eq_dec x value); [contradiction | lia].
Qed.
Lemma frequency_table_remove_head__window_semantics :
  forall x xs table,
    0 <= x < 1000001 ->
    FrequencyTable (x :: xs) table ->
    FrequencyTable xs (replace_Znth x (Znth x table 0 - 1) table).
Proof.
  intros x xs table Hx [Hlen Htable]. split.
  - rewrite Zlength_replace_Znth__window_semantics. exact Hlen.
  - intros value Hvalue.
    specialize (Htable value Hvalue).
    rewrite occurrences_cons__window_semantics in Htable.
    destruct (Z.eq_dec x value) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      destruct (Z.eq_dec value value); [lia | contradiction].
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (Z.eq_dec x value); [contradiction | lia].
Qed.
Lemma frequency_table_push__window_semantics :
  forall xs table i,
    0 <= i < Zlength xs ->
    0 <= Znth i xs 0 < 1000001 ->
    FrequencyTable (sublist 0 i xs) table ->
    FrequencyTable (sublist 0 (i + 1) xs)
      (replace_Znth (Znth i xs 0)
        (Znth (Znth i xs 0) table 0 + 1) table).
Proof.
  intros xs table i Hi Hvalue Htable.
  rewrite sublist_prefix_snoc__window_semantics by exact Hi.
  apply frequency_table_app_single__window_semantics; assumption.
Qed.
Lemma frequency_table_slide__window_semantics :
  forall xs table i m,
    0 < m ->
    m <= i < Zlength xs ->
    0 <= Znth (i - m) xs 0 < 1000001 ->
    0 <= Znth i xs 0 < 1000001 ->
    FrequencyTable (sublist (i - m) i xs) table ->
    FrequencyTable (sublist (i + 1 - m) (i + 1) xs)
      (replace_Znth (Znth i xs 0)
        (Znth (Znth i xs 0)
          (replace_Znth (Znth (i - m) xs 0)
            (Znth (Znth (i - m) xs 0) table 0 - 1) table) 0 + 1)
        (replace_Znth (Znth (i - m) xs 0)
          (Znth (Znth (i - m) xs 0) table 0 - 1) table)).
Proof.
  intros xs table i m Hm Hi Hout Hin Htable.
  assert (Hold :
    sublist (i - m) i xs =
      Znth (i - m) xs 0 :: sublist (i - m + 1) i xs).
  {
    rewrite (sublist_split (i - m) i (i - m + 1) xs) by lia.
    rewrite (sublist_single 0 (i - m) xs) by lia.
    reflexivity.
  }
  assert (Hnew :
    sublist (i + 1 - m) (i + 1) xs =
      sublist (i - m + 1) i xs ++ Znth i xs 0 :: nil).
  {
    replace (i + 1 - m) with (i - m + 1) by lia.
    rewrite (sublist_split (i - m + 1) (i + 1) i xs) by lia.
    rewrite (sublist_single 0 i xs) by lia.
    reflexivity.
  }
  rewrite Hold in Htable. rewrite Hnew.
  apply frequency_table_app_single__window_semantics; [exact Hin |].
  apply frequency_table_remove_head__window_semantics; assumption.
Qed.
Lemma sum_eq_indicator__window_semantics :
  forall x,
    0 <= x < 1000001 ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => if Z.eq_dec x value then 1 else 0) = 1.
Proof.
  intros x Hx.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 x 1000001) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split x (x + 1) 1000001) by lia.
  rewrite SumLib.ZRange.sum_Z_range_single.
  rewrite (SumLib.ZRange.sum_Z_range_eq_zero 0 x).
  2:{ intros value Hvalue. destruct (Z.eq_dec x value); [lia | reflexivity]. }
  rewrite (SumLib.ZRange.sum_Z_range_eq_zero (x + 1) 1000001).
  2:{ intros value Hvalue. destruct (Z.eq_dec x value); [lia | reflexivity]. }
  destruct (Z.eq_dec x x); [lia | contradiction].
Qed.
Lemma occurrences_mass__window_semantics :
  forall xs,
    Forall (fun x => 0 <= x < 1000001) xs ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Occurrences xs value) = Zlength xs.
Proof.
  intros xs Hbounds. induction Hbounds as [|x xs Hx Hbounds IH].
  - rewrite SumLib.ZRange.sum_Z_range_eq_zero.
    + reflexivity.
    + intros value Hvalue. rewrite occurrences_count_occ__window_semantics.
      reflexivity.
  - assert (Hext :
      SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
        (fun value => Occurrences (x :: xs) value) =
      SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
        (fun value => Occurrences xs value +
          (if Z.eq_dec x value then 1 else 0))).
    {
      apply SumLib.ZRange.sum_Z_range_ext.
      intros value Hvalue. apply occurrences_cons__window_semantics.
    }
    rewrite Hext.
    rewrite SumLib.ZRange.sum_Z_range_add.
    change
      (SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
         (fun value => Occurrences xs value) +
       SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
         (fun value => if Z.eq_dec x value then 1 else 0) =
       Zlength (x :: xs)).
    rewrite IH.
    rewrite sum_eq_indicator__window_semantics by exact Hx.
    rewrite Zlength_cons. lia.
Qed.
Lemma table_match_score_bounds__window_semantics :
  forall need_xs have_xs need have score,
    Forall (fun x => 0 <= x < 1000001) need_xs ->
    Forall (fun x => 0 <= x < 1000001) have_xs ->
    FrequencyTable need_xs need ->
    FrequencyTable have_xs have ->
    TableMatchScore need have score ->
    0 <= score <= Zlength have_xs.
Proof.
  intros need_xs have_xs need have score Hneedb Hhaveb
    [Hneedlen Hneed] [Hhavelen Hhave] Hscore.
  unfold TableMatchScore in Hscore. subst score. split.
  - apply SumLib.Sum.sum_nonneg. intros value Hvalue.
    rewrite Hneed by exact Hvalue. rewrite Hhave by exact Hvalue.
    pose proof (occurrences_nonneg__window_semantics need_xs value).
    pose proof (occurrences_nonneg__window_semantics have_xs value).
    apply Z.min_glb; assumption.
  - rewrite <- (occurrences_mass__window_semantics have_xs Hhaveb).
    apply SumLib.Sum.sum_le. intros value Hvalue.
    rewrite Hhave by exact Hvalue.
    apply Z.le_min_r.
Qed.
Lemma counted_good_windows_step__window_semantics :
  forall k values b upto answer,
    0 <= upto ->
    CountedGoodWindows k values b upto answer ->
    (GoodWindow b
       (sublist upto (upto + Zlength b) values) k ->
     CountedGoodWindows k values b (upto + 1) (answer + 1)) /\
    (~ GoodWindow b
       (sublist upto (upto + Zlength b) values) k ->
     CountedGoodWindows k values b (upto + 1) answer).
Proof.
  intros k values b upto answer Hupto Hcounted. split; intro Hnew;
    unfold CountedGoodWindows in *; subst answer.
  - rewrite set_card_Z_extend_true__window_semantics; [reflexivity | lia |].
    replace (upto + Zlength b) with (upto + Zlength b) by reflexivity.
    exact Hnew.
  - rewrite set_card_Z_extend_false__window_semantics; [reflexivity | lia |].
    exact Hnew.
Qed.
Lemma intersection_score_nil_l__window_semantics :
  forall ys,
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences nil value) (Occurrences ys value)) = 0.
Proof.
  intros ys.
  apply SumLib.ZRange.sum_Z_range_eq_zero. intros value Hvalue.
  rewrite occurrences_count_occ__window_semantics. simpl.
  rewrite Z.min_l by apply occurrences_nonneg__window_semantics.
  reflexivity.
Qed.
Lemma intersection_score_permutation_r__window_semantics :
  forall xs ys zs,
    Permutation ys zs ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value)) =
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences zs value)).
Proof.
  intros xs ys zs Hperm.
  apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
  rewrite !occurrences_count_occ__window_semantics.
  f_equal. f_equal.
  exact ((proj1 (Permutation_count_occ Z.eq_dec ys zs)) Hperm value).
Qed.
Lemma intersection_score_cons_same__window_semantics :
  forall x xs ys,
    0 <= x < 1000001 ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences (x :: xs) value)
        (Occurrences (x :: ys) value)) =
    1 + SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value)).
Proof.
  intros x xs ys Hx.
  assert (Hext :
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences (x :: xs) value)
        (Occurrences (x :: ys) value)) =
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value) +
        (if Z.eq_dec x value then 1 else 0))).
  {
    apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
    rewrite !occurrences_cons__window_semantics.
    destruct (Z.eq_dec x value); [rewrite Z.add_min_distr_r; lia | lia].
  }
  rewrite Hext, SumLib.ZRange.sum_Z_range_add.
  rewrite sum_eq_indicator__window_semantics by exact Hx. ring.
Qed.
Lemma intersection_score_cons_le__window_semantics :
  forall x y xs ys,
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value)) <=
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences (x :: xs) value)
        (Occurrences (y :: ys) value)).
Proof.
  intros x y xs ys.
  apply SumLib.Sum.sum_le. intros value Hvalue.
  rewrite !occurrences_cons__window_semantics.
  pose proof (occurrences_nonneg__window_semantics xs value).
  pose proof (occurrences_nonneg__window_semantics ys value).
  destruct (Z.eq_dec x value); destruct (Z.eq_dec y value); simpl; lia.
Qed.
Lemma permutation_cons_present__window_semantics :
  forall x ys,
    In x ys -> exists rest : list Z, Permutation ys (x :: rest).
Proof.
  intros x ys. induction ys as [|y ys IH]; intro Hin; [contradiction |].
  simpl in Hin.
  destruct (Z.eq_dec x y) as [Hxy | Hxy].
  - subst y. exists ys. apply Permutation_refl.
  -
    destruct Hin as [Hbad | Hin]; [congruence |].
    destruct (IH Hin) as [rest Hperm]. exists (y :: rest).
    eapply Permutation_trans.
    + apply perm_skip. exact Hperm.
    + apply perm_swap.
Qed.
Lemma intersection_score_cons_present__window_semantics :
  forall x xs ys rest,
    0 <= x < 1000001 ->
    Permutation ys (x :: rest) ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences (x :: xs) value)
        (Occurrences ys value)) =
    1 + SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value)
        (Occurrences rest value)).
Proof.
  intros x xs ys rest Hx Hperm.
  rewrite (intersection_score_permutation_r__window_semantics
    (x :: xs) ys (x :: rest) Hperm).
  apply intersection_score_cons_same__window_semantics. exact Hx.
Qed.
Lemma intersection_score_cons_absent__window_semantics :
  forall x xs ys,
    0 <= x < 1000001 ->
    ~ In x ys ->
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences (x :: xs) value)
        (Occurrences ys value)) =
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value)).
Proof.
  intros x xs ys Hx Hnot.
  apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
  rewrite occurrences_cons__window_semantics.
  destruct (Z.eq_dec x value) as [-> | Hneq].
  - destruct (count_occ Z.eq_dec ys value) eqn:Hcount.
    + assert (Hzero : Occurrences ys value = 0).
      { rewrite occurrences_count_occ__window_semantics, Hcount. reflexivity. }
      rewrite Hzero. destruct (Z.eq_dec value value); [|contradiction].
      pose proof (occurrences_nonneg__window_semantics xs value) as Hnonneg.
      rewrite (Z.min_r (Occurrences xs value + 1) 0) by lia.
      rewrite (Z.min_r (Occurrences xs value) 0) by lia.
      reflexivity.
    + exfalso. apply Hnot. apply (proj2 (count_occ_In Z.eq_dec ys value)).
      rewrite Hcount. lia.
  - destruct (Z.eq_dec x value); [contradiction | f_equal; lia].
Qed.
Lemma matching_card_cons__window_semantics :
  forall x y xs ys,
    #(fun i : Z => 0 <= i < Zlength (x :: xs) /\
      Znth i (x :: xs) 0 = Znth i (y :: ys) 0) =
    (if Z.eq_dec x y then 1 else 0) +
    #(fun i : Z => 0 <= i < Zlength xs /\
      Znth i xs 0 = Znth i ys 0).
Proof.
  intros x y xs ys. rewrite !set_card_Z_as_sum__window_semantics.
  rewrite Zlength_cons.
  replace (Z.succ (Zlength xs)) with (Zlength xs + 1) by lia.
  rewrite SumLib.ZRange.sum_Z_range_cons by
    (pose proof (Zlength_nonneg xs); lia).
  change (fun i : Z => 0 + 1 <= i < Zlength xs + 1)
    with (fun i : Z => 0 + 1 <= i < Zlength xs + 1).
  rewrite SumLib.ZRange.sum_Z_range_shift_1.
  assert (Hhead :
    (if prop_dec
       (Znth 0 (x :: xs) 0 = Znth 0 (y :: ys) 0)
     then 1 else 0) = if Z.eq_dec x y then 1 else 0).
  {
    rewrite !Znth0_cons.
    destruct (Z.eq_dec x y); destruct (prop_dec (x = y));
      try reflexivity; contradiction.
  }
  replace (if Z.eq_dec x y then 1 else 0) with
    (if prop_dec
       (Znth 0 (x :: xs) 0 = Znth 0 (y :: ys) 0)
     then 1 else 0) by exact Hhead.
  f_equal.
  apply SumLib.ZRange.sum_Z_range_ext. intros i Hi.
  rewrite !Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  destruct (prop_dec (Znth i xs 0 = Znth i ys 0)); reflexivity.
Qed.
Lemma matching_card_sym__window_semantics :
  forall xs ys,
    #(fun i : Z => 0 <= i < Zlength xs /\
      Znth i ys 0 = Znth i xs 0) =
    #(fun i : Z => 0 <= i < Zlength xs /\
      Znth i xs 0 = Znth i ys 0).
Proof.
  intros xs ys. apply set_card_Z_iff__window_semantics.
  intro i. split; intros [Hi Heq]; split; [exact Hi | symmetry; exact Heq |
    exact Hi | symmetry; exact Heq].
Qed.
Lemma positional_matches_le_intersection__window_semantics :
  forall xs ys,
    Zlength xs = Zlength ys ->
    Forall (fun x => 0 <= x < 1000001) xs ->
    #(fun i : Z => 0 <= i < Zlength xs /\
      Znth i xs 0 = Znth i ys 0) <=
    SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences xs value) (Occurrences ys value)).
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Hlen Hbounds.
  - destruct ys as [|y ys].
    + rewrite intersection_score_nil_l__window_semantics.
      rewrite set_card_Z_as_sum__window_semantics.
      rewrite SumLib.ZRange.sum_Z_range_empty by
        (rewrite Zlength_nil; lia).
      reflexivity.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. discriminate.
  - destruct ys as [|y ys].
    { rewrite !Zlength_correct in Hlen. simpl in Hlen. discriminate. }
    inversion Hbounds as [|? ? Hx Hbounds']; subst.
    rewrite matching_card_cons__window_semantics.
    rewrite !Zlength_cons in Hlen.
    specialize (IH ys ltac:(lia) Hbounds').
    destruct (Z.eq_dec x y) as [-> | Hneq].
    + rewrite intersection_score_cons_same__window_semantics by exact Hx. lia.
    + simpl. eapply Z.le_trans; [exact IH |].
      apply intersection_score_cons_le__window_semantics.
Qed.
Lemma chosen_option_length_le__window_semantics :
  forall ps : list (option Z),
    Zlength
      (flat_map (fun o => match o with
        | Some x => x :: nil
        | None => nil
        end) ps) <= Zlength ps.
Proof.
  intros ps. induction ps as [|o ps IH]; [reflexivity |].
  destruct o; simpl; rewrite !Zlength_cons; lia.
Qed.
Lemma alignment_pattern_exists__window_semantics :
  forall b w,
    Forall (fun x => 0 <= x < 1000001) b ->
    exists (ps : list (option Z)) (rem : list Z),
      Forall2 (fun x o => o = None \/ o = Some x) b ps /\
      Permutation w
        (flat_map (fun o => match o with
          | Some x => x :: nil
          | None => nil
          end) ps ++ rem) /\
      SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
        (fun value => Z.min (Occurrences b value) (Occurrences w value)) =
      Zlength
        (flat_map (fun o => match o with
          | Some x => x :: nil
          | None => nil
          end) ps).
Proof.
  intros b. induction b as [|x b IH]; intros w Hbounds.
  - exists nil, w. split; [constructor |]. split.
    + apply Permutation_refl.
    + rewrite intersection_score_nil_l__window_semantics. reflexivity.
  - inversion Hbounds as [|? ? Hx Hbounds']; subst.
    destruct (in_dec Z.eq_dec x w) as [Hin | Hnot].
    + destruct (permutation_cons_present__window_semantics x w Hin)
        as [rest Hpermhead].
      destruct (IH rest Hbounds') as [ps [rem [Halign [Hperm Hscore]]]].
      exists (Some x :: ps), rem. split.
      * constructor; [right; reflexivity | exact Halign].
      * split.
        -- simpl. eapply Permutation_trans; [exact Hpermhead |].
           apply perm_skip. exact Hperm.
        -- simpl. rewrite (intersection_score_cons_present__window_semantics
             x b w rest Hx Hpermhead), Hscore.
           rewrite Zlength_cons. lia.
    + destruct (IH w Hbounds') as [ps [rem [Halign [Hperm Hscore]]]].
      exists (None :: ps), rem. split.
      * constructor; [left; reflexivity | exact Halign].
      * split.
        -- simpl. exact Hperm.
        -- simpl. rewrite (intersection_score_cons_absent__window_semantics
             x b w Hx Hnot), Hscore. reflexivity.
Qed.
Lemma fill_alignment_pattern__window_semantics :
  forall b ps rem,
    Forall2 (fun x o => o = None \/ o = Some x) b ps ->
    Zlength b =
      Zlength
        (flat_map (fun o => match o with
          | Some x => x :: nil
          | None => nil
          end) ps ++ rem) ->
    exists rearranged,
      Permutation
        (flat_map (fun o => match o with
          | Some x => x :: nil
          | None => nil
          end) ps ++ rem) rearranged /\
      Zlength rearranged = Zlength b /\
      Zlength
        (flat_map (fun o => match o with
          | Some x => x :: nil
          | None => nil
          end) ps) <=
      #(fun i : Z => 0 <= i < Zlength b /\
        Znth i rearranged 0 = Znth i b 0).
Proof.
  intros b ps rem Halign. revert rem.
  induction Halign as [|x o b ps Ho Halign IH]; intros rem Hlen.
  - simpl in Hlen. rewrite Zlength_nil in Hlen.
    destruct rem as [|r rem].
    + exists nil. repeat split; try constructor; reflexivity.
    + rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg rem). lia.
  - destruct Ho as [-> | ->].
    + simpl in Hlen.
      assert (Hpslen : Zlength ps = Zlength b).
      { rewrite !Zlength_correct. f_equal. apply Forall2_length in Halign.
        exact (eq_sym Halign). }
      destruct rem as [|y rem].
      {
        rewrite app_nil_r in Hlen.
        pose proof (chosen_option_length_le__window_semantics ps).
        rewrite Zlength_cons in Hlen. lia.
      }
      rewrite Zlength_cons, Zlength_app, Zlength_cons in Hlen.
      assert (Htail :
        Zlength b =
        Zlength
          (flat_map (fun o => match o with
            | Some z => z :: nil
            | None => nil
            end) ps ++ rem)) by
        (rewrite Zlength_app; lia).
      destruct (IH rem Htail) as [r [Hperm [Hrlen Hmatches]]].
      exists (y :: r). split.
      * eapply Permutation_trans.
        -- apply Permutation_sym. apply Permutation_middle.
        -- apply perm_skip. exact Hperm.
      * split.
        -- rewrite Zlength_cons, Hrlen, Zlength_cons. reflexivity.
        -- simpl. rewrite matching_card_sym__window_semantics.
           rewrite matching_card_cons__window_semantics.
           rewrite matching_card_sym__window_semantics in Hmatches.
           eapply Z.le_trans; [exact Hmatches |].
           assert (0 <= (if Z.eq_dec x y then 1 else 0)) by
             (destruct (Z.eq_dec x y); lia).
           lia.
    + simpl in Hlen.
      rewrite !Zlength_cons in Hlen.
      destruct (IH rem ltac:(lia)) as [r [Hperm [Hrlen Hmatches]]].
      exists (x :: r). split.
      * apply perm_skip. exact Hperm.
      * split.
        -- rewrite Zlength_cons, Hrlen, Zlength_cons. reflexivity.
        -- simpl. rewrite matching_card_sym__window_semantics.
           rewrite matching_card_cons__window_semantics.
           rewrite matching_card_sym__window_semantics in Hmatches.
           destruct (Z.eq_dec x x); [rewrite Zlength_cons; lia | contradiction].
Qed.
Lemma match_score_attainable__window_semantics :
  forall b w,
    Zlength b = Zlength w ->
    Forall (fun x => 0 <= x < 1000001) b ->
    exists rearranged,
      Permutation w rearranged /\
      Zlength rearranged = Zlength b /\
      SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
        (fun value => Z.min (Occurrences b value) (Occurrences w value)) <=
      #(fun i : Z => 0 <= i < Zlength b /\
        Znth i rearranged 0 = Znth i b 0).
Proof.
  intros b w Hlen Hbounds.
  destruct (alignment_pattern_exists__window_semantics b w Hbounds)
    as [ps [rem [Halign [Hperm Hscore]]]].
  assert (Hfilllen :
    Zlength b =
    Zlength
      (flat_map (fun o => match o with
        | Some x => x :: nil
        | None => nil
        end) ps ++ rem)).
  {
    rewrite Hlen.
    rewrite !Zlength_correct.
    f_equal. apply Permutation_length in Hperm. exact Hperm.
  }
  destruct (fill_alignment_pattern__window_semantics b ps rem Halign Hfilllen)
    as [rearranged [Hfillperm [Hrlen Hmatches]]].
  exists rearranged. split.
  - eapply Permutation_trans; eassumption.
  - split; [exact Hrlen |]. rewrite Hscore. exact Hmatches.
Qed.
Lemma Forall_Znth_intro__window_semantics :
  forall (xs : list Z) (P : Z -> Prop),
    (forall i, 0 <= i < Zlength xs -> P (Znth i xs 0)) ->
    Forall P xs.
Proof.
  intros xs. induction xs as [|x xs IH]; intros P Hall; constructor.
  - apply (Hall 0). rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
  - apply IH. intros i Hi.
    specialize (Hall (i + 1) ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth_cons in Hall by lia. replace (i + 1 - 1) with i in Hall by lia.
    exact Hall.
Qed.
Lemma good_window_iff_match_score__window_semantics :
  forall b window need have score k,
    Zlength b = Zlength window ->
    (forall i, 0 <= i < Zlength b -> 0 <= Znth i b 0 < 1000001) ->
    (forall i, 0 <= i < Zlength window ->
      0 <= Znth i window 0 < 1000001) ->
    FrequencyTable b need ->
    FrequencyTable window have ->
    TableMatchScore need have score ->
    (GoodWindow b window k <-> score >= k).
Proof.
  intros b window need have score k Hlen Hbnd Wbnd
    [Hneedlen Hneed] [Hhavelen Hhave] Hscore.
  assert (Hscoreeq :
    score = SumLib.Sum.sum (fun value : Z => 0 <= value < 1000001)
      (fun value => Z.min (Occurrences b value) (Occurrences window value))).
  {
    unfold TableMatchScore in Hscore. rewrite Hscore.
    apply SumLib.ZRange.sum_Z_range_ext. intros value Hvalue.
    rewrite Hneed by exact Hvalue. rewrite Hhave by exact Hvalue.
    reflexivity.
  }
  split.
  - intros [rearranged [Hperm [Hrlen Hmatched]]].
    assert (HbForall : Forall (fun x => 0 <= x < 1000001) b).
    { apply Forall_Znth_intro__window_semantics. exact Hbnd. }
    pose proof (positional_matches_le_intersection__window_semantics
      b rearranged (eq_sym Hrlen) HbForall) as Hupper.
    rewrite <- (intersection_score_permutation_r__window_semantics
      b window rearranged Hperm) in Hupper.
    rewrite matching_card_sym__window_semantics in Hmatched.
    rewrite Hscoreeq. lia.
  - intro Hge.
    assert (HbForall : Forall (fun x => 0 <= x < 1000001) b).
    { apply Forall_Znth_intro__window_semantics. exact Hbnd. }
    destruct (match_score_attainable__window_semantics b window Hlen HbForall)
      as [rearranged [Hperm [Hrlen Hmatched]]].
    exists rearranged. split; [exact Hperm |]. split; [exact Hrlen |].
    rewrite Hscoreeq in Hge. lia.
Qed.
Lemma counted_good_windows_zero__window_semantics :
  forall k values b,
    CountedGoodWindows k values b 0 0.
Proof.
  intros k values b. unfold CountedGoodWindows.
  rewrite set_card_Z_as_sum__window_semantics.
  symmetry. apply SumLib.ZRange.sum_Z_range_eq_zero.
  intros value Hvalue. lia.
Qed.
Lemma sublist_Znth_bounds__window_semantics :
  forall xs lo hi,
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    (forall i, 0 <= i < Zlength xs ->
      0 <= Znth i xs 0 < 1000001) ->
    forall j, 0 <= j < Zlength (sublist lo hi xs) ->
      0 <= Znth j (sublist lo hi xs) 0 < 1000001.
Proof.
  intros xs lo hi Hlo Hhi Hbnd j Hj.
  rewrite Zlength_sublist in Hj by lia.
  rewrite Znth_sublist by lia.
  apply Hbnd. lia.
Qed.
Lemma Zlength_replace_Znth__cleanup_and_result :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma cleared_by_prefix_zero__cleanup_and_result :
  forall source table,
    Zlength table = 1000001 ->
    ClearedByPrefix table source 0 table.
Proof.
  intros source table Hlen.
  unfold ClearedByPrefix.
  split.
  - exact Hlen.
  - split.
    + intros value Hvalue _.
      reflexivity.
    + intros j Hj.
      lia.
Qed.
Lemma cleared_by_prefix_step__cleanup_and_result :
  forall original source table i,
    0 <= i < Zlength source ->
    (forall j, 0 <= j <= i -> 0 <= Znth j source 0 < 1000001) ->
    ClearedByPrefix original source i table ->
    ClearedByPrefix original source (i + 1)
      (replace_Znth (Znth i source 0) 0 table).
Proof.
  intros original source table i Hi Hsource Hcleared.
  unfold ClearedByPrefix in *.
  destruct Hcleared as [Hlen [Hsame Hzero]].
  repeat split.
  - rewrite Zlength_replace_Znth__cleanup_and_result.
    exact Hlen.
  - intros value Hvalue Habsent.
    assert (Hcurrent : Znth i source 0 <> value).
    { intro Heq. apply (Habsent i); lia. }
    rewrite Znth_replace_Znth_Diff.
    + apply Hsame; try assumption.
      intros j Hj Heq.
      apply (Habsent j); lia.
    + specialize (Hsource i ltac:(lia)). lia.
    + rewrite Hlen. lia.
    + exact Hcurrent.
  - intros j Hj.
    assert (Hjbound : 0 <= j <= i) by lia.
    specialize (Hsource j Hjbound) as Hsourcej.
    destruct (Z.eq_dec (Znth i source 0) (Znth j source 0)) as [Heq | Hneq].
    + rewrite <- Heq.
      rewrite Znth_replace_Znth_Same.
      * reflexivity.
      * specialize (Hsource i ltac:(lia)). rewrite Hlen. lia.
    + rewrite Znth_replace_Znth_Diff.
      * apply Hzero.
        assert (j <> i).
        { intro Heqji. subst j. apply Hneq. reflexivity. }
        lia.
      * specialize (Hsource i ltac:(lia)). rewrite Hlen. lia.
      * rewrite Hlen. lia.
      * exact Hneq.
Qed.
Lemma cleared_frequency_table_complete__cleanup_and_result :
  forall source tracked original table,
    FrequencyTable tracked original ->
    (forall j, 0 <= j < Zlength tracked ->
      exists i, 0 <= i < Zlength source /\
        Znth j tracked 0 = Znth i source 0) ->
    ClearedByPrefix original source (Zlength source) table ->
    table = repeat 0 (Z.to_nat 1000001).
Proof.
  intros source tracked original table Hfrequency Hcoverage Hcleared.
  unfold FrequencyTable in Hfrequency.
  unfold ClearedByPrefix in Hcleared.
  destruct Hfrequency as [Horiginal_len Hfrequency].
  destruct Hcleared as [Htable_len [Hsame Hzero]].
  apply (proj2 (list_eq_ext table (repeat 0 (Z.to_nat 1000001)) 0)).
  split.
  - rewrite Htable_len.
    rewrite Zlength_correct, repeat_length.
    lia.
  - intros value Hvalue.
    rewrite Htable_len in Hvalue.
    rewrite Znth_repeat.
    destruct (classic (exists j, 0 <= j < Zlength source /\
      Znth j source 0 = value)) as [[j [Hj Heq]] | Hnone].
    + rewrite <- Heq.
      apply Hzero.
      exact Hj.
    + rewrite Hsame; try lia.
      * rewrite Hfrequency by lia.
        unfold Occurrences, set_card.
        rewrite (SumLib.Sum.sum_ext
          (fun j : Z => 0 <= j < Zlength tracked /\ Znth j tracked 0 = value)
          (fun _ => 1) (fun _ => 0)).
        -- apply SumLib.Sum.sum_zero.
        -- intros j Hj.
           exfalso.
           destruct (Hcoverage j (proj1 Hj)) as [i [Hi Heq]].
           apply Hnone.
           exists i.
           split; try assumption.
           rewrite <- Heq.
           exact (proj2 Hj).
      * intros j Hj Heq.
        apply Hnone.
        exists j.
        auto.
Qed.
Lemma counted_good_windows_spec_bridge__cleanup_and_result :
  forall k values b answer,
    CountedGoodWindows k values b
      (Zlength values - Zlength b + 1) answer ->
    Spec k values b answer.
Proof.
  intros k values b answer Hcounted.
  unfold CountedGoodWindows in Hcounted.
  unfold Spec.
  exact Hcounted.
Qed.
