Require Import Coq.ZArith.ZArith Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import ListLib.Base.Positional ListLib.General.Length.
Local Open Scope Z_scope.

Definition hp_hash (previous current : Z) : Z := (current - 8 * previous) mod 256.
Definition hp_hash_at (bytes : list Z) (position : Z) : Z :=
  hp_hash (Znth (position - 1) bytes 0) (Znth position bytes 0).

Definition hp_inputs (bytes : list Z) (length hayoff haylen needleoff needlelen : Z) : Prop :=
  Zlength bytes = length /\ 0 <= length <= 2147483647 /\
  0 <= hayoff /\ 0 <= haylen /\ hayoff + haylen <= length /\
  0 <= needleoff /\ 3 <= needlelen <= 256 /\ needleoff + needlelen <= length /\
  Forall (fun value => 0 <= value <= 255) bytes.

Definition hp_match_at (bytes : list Z) (hayoff haylen needleoff needlelen position : Z) : Prop :=
  0 <= position /\ position + needlelen <= haylen /\
  forall index, 0 <= index < needlelen ->
    Znth (hayoff + position + index) bytes 0 = Znth (needleoff + index) bytes 0.

Definition hp_no_match_before (bytes : list Z) (hayoff haylen needleoff needlelen bound : Z) : Prop :=
  forall position, 0 <= position < bound ->
    ~ hp_match_at bytes hayoff haylen needleoff needlelen position.

Definition hp_result (bytes : list Z) (base hayoff haylen needleoff needlelen result : Z) : Prop :=
  (result = 0 /\ forall position, ~ hp_match_at bytes hayoff haylen needleoff needlelen position) \/
  exists position, result = base + hayoff + position /\
    hp_match_at bytes hayoff haylen needleoff needlelen position /\
    hp_no_match_before bytes hayoff haylen needleoff needlelen position.

Definition hp_rightmost (bytes : list Z) (needleoff prefix hash value : Z) : Prop :=
  0 <= value < prefix /\
  (value = 0 \/ (1 <= value /\ hp_hash_at bytes (needleoff + value) = hash)) /\
  forall index, 1 <= index < prefix -> hp_hash_at bytes (needleoff + index) = hash -> index <= value.

Definition hp_table_prefix (bytes : list Z) (needleoff prefix : Z) (table : list Z) : Prop :=
  Zlength table = 256 /\
  forall hash, 0 <= hash < 256 -> hp_rightmost bytes needleoff prefix hash (Znth hash table 0).

Definition hp_table_final (bytes : list Z) (needleoff needlelen : Z) (table : list Z) (shift1 : Z) : Prop :=
  exists internal,
    hp_table_prefix bytes needleoff (needlelen - 1) internal /\
    shift1 = needlelen - 1 - Znth (hp_hash_at bytes (needleoff + needlelen - 1)) internal 0 /\
    table = replace_Znth (hp_hash_at bytes (needleoff + needlelen - 1)) (needlelen - 1) internal.

Definition hp_filter_offset (last offset : Z) : Prop :=
  15 <= last -> 0 <= offset /\ offset + 8 <= last.

Definition hp_memcmp_result (bytes : list Z) (left right count result : Z) : Prop :=
  result = 0 <-> forall index, 0 <= index < count ->
    Znth (left + index) bytes 0 = Znth (right + index) bytes 0.

Require Import Coq.micromega.Psatz.

(* Helper lemmas migrated from horspool_memmem__merged_proof_manual.v. *)

Lemma hp_hash_pair_congruence : forall previous1 current1 previous2 current2,
  previous1 = previous2 -> current1 = current2 ->
  hp_hash previous1 current1 = hp_hash previous2 current2.
Proof. intros; subst; reflexivity. Qed.

Lemma hp_hash_last_byte_injective : forall previous current1 current2,
  0 <= current1 < 256 -> 0 <= current2 < 256 ->
  hp_hash previous current1 = hp_hash previous current2 -> current1 = current2.
Proof.
  intros previous current1 current2 Range1 Range2 Hash.
  unfold hp_hash in Hash.
  apply (f_equal (fun value => (value + 8 * previous) mod 256)) in Hash.
  cbv beta in Hash.
  repeat rewrite Zplus_mod_idemp_l in Hash.
  replace (current1 - 8 * previous + 8 * previous) with current1 in Hash by ring.
  replace (current2 - 8 * previous + 8 * previous) with current2 in Hash by ring.
  rewrite (Z.mod_small _ _ Range1), (Z.mod_small _ _ Range2) in Hash.
  exact Hash.
Qed.

Lemma hp_match_implies_pair_hash : forall bytes hayoff haylen needleoff needlelen position index,
  hp_match_at bytes hayoff haylen needleoff needlelen position ->
  1 <= index < needlelen ->
  hp_hash_at bytes (hayoff + position + index) = hp_hash_at bytes (needleoff + index).
Proof.
  intros bytes hayoff haylen needleoff needlelen position index [_ [_ Equal]] Index.
  unfold hp_hash_at.
  replace (hayoff + position + index - 1) with (hayoff + position + (index - 1)) by ring.
  replace (needleoff + index - 1) with (needleoff + (index - 1)) by ring.
  rewrite (Equal index), (Equal (index - 1)); try lia; reflexivity.
Qed.

Lemma hp_final_table_dominates : forall bytes needleoff needlelen table shift1 hash index,
  hp_table_final bytes needleoff needlelen table shift1 ->
  3 <= needlelen -> 0 <= hash < 256 -> 1 <= index < needlelen ->
  hp_hash_at bytes (needleoff + index) = hash -> index <= Znth hash table 0.
Proof.
  intros bytes needleoff needlelen table shift1 hash index
    [internal [[Length Rightmost] [Shift Table]]] Needle Hash Index Equal.
  subst table.
  assert (TailRange : 0 <= hp_hash_at bytes (needleoff + needlelen - 1) < 256)
    by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec (hp_hash_at bytes (needleoff + needlelen - 1)) hash) as [Same | Different].
  - rewrite Same, Znth_replace_Znth_Same by lia. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    assert (InternalIndex : index < needlelen - 1).
    { destruct (Z.eq_dec index (needlelen - 1)) as [Last | Earlier]; [|lia].
      subst index. exfalso. apply Different.
      replace (needleoff + needlelen - 1) with (needleoff + (needlelen - 1)) by ring.
      exact Equal. }
    specialize (Rightmost hash Hash).
    destruct Rightmost as [_ [_ Maximum]]. apply Maximum; auto; lia.
Qed.

Lemma hp_endpoint_skip : forall bytes hayoff haylen needleoff needlelen table shift1 endpoint value,
  hp_table_final bytes needleoff needlelen table shift1 -> 3 <= needlelen ->
  0 <= value <= needlelen - 1 ->
  value = Znth (hp_hash_at bytes (hayoff + endpoint)) table 0 ->
  hp_no_match_before bytes hayoff haylen needleoff needlelen (endpoint - (needlelen - 1)) ->
  hp_no_match_before bytes hayoff haylen needleoff needlelen (endpoint - value).
Proof.
  intros bytes hayoff haylen needleoff needlelen table shift1 endpoint value
    Table Needle Value Lookup Before position Position Match.
  destruct (Z_lt_ge_dec position (endpoint - (needlelen - 1))) as [Earlier | NewlySkipped].
  - apply (Before position); [lia | exact Match].
  - assert (Index : 1 <= endpoint - position < needlelen) by lia.
    pose proof (hp_match_implies_pair_hash bytes hayoff haylen needleoff needlelen position
      (endpoint - position) Match Index) as Hash.
    replace (hayoff + position + (endpoint - position)) with (hayoff + endpoint) in Hash by ring.
    assert (HashRange : 0 <= hp_hash_at bytes (hayoff + endpoint) < 256)
      by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
    pose proof (hp_final_table_dominates bytes needleoff needlelen table shift1
      (hp_hash_at bytes (hayoff + endpoint)) (endpoint - position)
      Table Needle HashRange Index (eq_sym Hash)) as Bound.
    rewrite <- Lookup in Bound. lia.
Qed.

Lemma hp_shift1_positive : forall bytes needleoff needlelen table shift1,
  hp_table_final bytes needleoff needlelen table shift1 -> 3 <= needlelen ->
  1 <= shift1 <= needlelen - 1.
Proof.
  intros bytes needleoff needlelen table shift1
    [internal [[Length Rightmost] [Shift Table]]] Needle.
  assert (HashRange : 0 <= hp_hash_at bytes (needleoff + needlelen - 1) < 256)
    by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
  specialize (Rightmost _ HashRange). destruct Rightmost as [Bound _]. lia.
Qed.

Lemma hp_tail_aligned_mismatch_skip : forall bytes hayoff haylen needleoff needlelen table shift1 position,
  hp_table_final bytes needleoff needlelen table shift1 -> 3 <= needlelen ->
  hp_hash_at bytes (hayoff + position + (needlelen - 1)) =
    hp_hash_at bytes (needleoff + needlelen - 1) ->
  hp_no_match_before bytes hayoff haylen needleoff needlelen position ->
  ~ hp_match_at bytes hayoff haylen needleoff needlelen position ->
  hp_no_match_before bytes hayoff haylen needleoff needlelen (position + shift1).
Proof.
  intros bytes hayoff haylen needleoff needlelen table shift1 position
    Table Needle Tail Before Mismatch candidate Candidate Match.
  pose proof (hp_shift1_positive bytes needleoff needlelen table shift1 Table Needle) as ShiftBounds.
  destruct (Z_lt_ge_dec candidate position) as [Earlier | Later].
  - apply (Before candidate); [lia | exact Match].
  - destruct (Z.eq_dec candidate position) as [Same | Different].
    + subst candidate. exact (Mismatch Match).
    + destruct Table as [internal [[Length Rightmost] [Shift Table]]].
      assert (Index : 1 <= position + (needlelen - 1) - candidate < needlelen - 1) by lia.
      pose proof (hp_match_implies_pair_hash bytes hayoff haylen needleoff needlelen candidate
        (position + (needlelen - 1) - candidate) Match ltac:(lia)) as Hash.
      replace (hayoff + candidate + (position + (needlelen - 1) - candidate))
        with (hayoff + position + (needlelen - 1)) in Hash by ring.
      assert (HashRange : 0 <= hp_hash_at bytes (needleoff + needlelen - 1) < 256)
        by (unfold hp_hash_at, hp_hash; apply Z.mod_pos_bound; lia).
      specialize (Rightmost _ HashRange). destruct Rightmost as [_ [_ Maximum]].
      specialize (Maximum (position + (needlelen - 1) - candidate) Index).
      assert (Equal : hp_hash_at bytes (needleoff + (position + (needlelen - 1) - candidate)) =
        hp_hash_at bytes (needleoff + needlelen - 1)) by congruence.
      specialize (Maximum Equal). lia.
Qed.

Lemma hp_memcmp_failure_excludes_match : forall bytes hayoff haylen needleoff needlelen position offset count result,
  0 <= offset -> 0 <= count -> offset + count <= needlelen -> result <> 0 ->
  hp_memcmp_result bytes (hayoff + position + offset) (needleoff + offset) count result ->
  ~ hp_match_at bytes hayoff haylen needleoff needlelen position.
Proof.
  intros bytes hayoff haylen needleoff needlelen position offset count result
    Offset Count Bound Nonzero Compare [_ [_ Equal]].
  apply Nonzero. apply (proj2 Compare). intros index Index.
  replace (hayoff + position + offset + index) with (hayoff + position + (offset + index)) by ring.
  replace (needleoff + offset + index) with (needleoff + (offset + index)) by ring.
  apply Equal. lia.
Qed.

Lemma hp_rank_strict_decrease : forall bound before after,
  before <= bound -> before < after ->
  (Z.to_nat (bound + 1 - after) < Z.to_nat (bound + 1 - before))%nat.
Proof.
  intros bound before after Guard Advance.
  destruct (Z_le_gt_dec 0 (bound + 1 - after)) as [Nonnegative | Negative].
  - apply (proj1 (Z2Nat.inj_lt (bound + 1 - after) (bound + 1 - before) Nonnegative ltac:(lia))). lia.
  - assert (Zero : Z.to_nat (bound + 1 - after) = 0%nat).
    { destruct (bound + 1 - after); simpl; try reflexivity; lia. }
    rewrite Zero.
    apply (proj1 (Z2Nat.inj_lt 0 (bound + 1 - before) ltac:(lia) ltac:(lia))). lia.
Qed.

Lemma hp_table_build_rank : forall last index,
  index < last ->
  (Z.to_nat (last - (index + 1)) < Z.to_nat (last - index))%nat.
Proof.
  intros last index Guard.
  replace (last - (index + 1)) with ((last - 1) + 1 - (index + 1)) by ring.
  replace (last - index) with ((last - 1) + 1 - index) by ring.
  apply hp_rank_strict_decrease; lia.
Qed.

Lemma hp_zero_lookup_rank : forall bound endpoint last,
  endpoint <= bound -> 2 <= last ->
  endpoint < endpoint + last /\
  (Z.to_nat (bound + 1 - (endpoint + last)) <
   Z.to_nat (bound + 1 - endpoint))%nat.
Proof.
  intros bound endpoint last Guard Last.
  split; [lia | apply hp_rank_strict_decrease; lia].
Qed.

Lemma hp_realign_outer_rank : forall bound position last scan_steps table_value,
  position <= bound -> 2 <= last -> 1 <= scan_steps ->
  0 <= table_value < last ->
  position < position + scan_steps * last - table_value /\
  (Z.to_nat (bound + 1 - (position + scan_steps * last - table_value)) <
   Z.to_nat (bound + 1 - position))%nat.
Proof.
  intros bound position last scan_steps table_value Guard Last Scans Value.
  assert (Advance : position < position + scan_steps * last - table_value) by nia.
  split; [exact Advance | apply hp_rank_strict_decrease; assumption].
Qed.

Lemma hp_mismatch_outer_rank : forall bound position last scan_steps shift1,
  position <= bound -> 2 <= last -> 1 <= scan_steps -> 1 <= shift1 ->
  position < position + (scan_steps - 1) * last + shift1 /\
  (Z.to_nat (bound + 1 - (position + (scan_steps - 1) * last + shift1)) <
   Z.to_nat (bound + 1 - position))%nat.
Proof.
  intros bound position last scan_steps shift1 Guard Last Scans Shift.
  assert (Advance : position < position + (scan_steps - 1) * last + shift1) by nia.
  split; [exact Advance | apply hp_rank_strict_decrease; assumption].
Qed.

Lemma hp_no_infinite_bounded_advancing_positions : forall bound (positions : nat -> Z),
  (forall step, positions step <= bound) ->
  (forall step, positions step < positions (S step)) -> False.
Proof.
  intros bound positions Bounded Advance.
  assert (Lower : forall step, positions O + Z.of_nat step <= positions step).
  { intro step; induction step as [| step IH].
    - simpl. lia.
    - rewrite Nat2Z.inj_succ. specialize (Advance step). lia. }
  pose proof (Bounded O) as Initial.
  specialize (Lower (Z.to_nat (bound - positions O + 1))).
  rewrite Z2Nat.id in Lower by lia.
  specialize (Bounded (Z.to_nat (bound - positions O + 1))). lia.
Qed.
