From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib two_way_match_long_needle shift_table_refinement.
Local Open Scope Z_scope.

(* A last occurrence in a periodic pattern lies in its final period.
   Thus musl's memory branch satisfies the original theorem's shift bound. *)
Lemma last_occurrence_period_distance : forall patn p last c,
  string_period patn p -> 0 <= last < Zlength patn ->
  Znth last patn 0 = c ->
  (forall t, last < t < Zlength patn -> Znth t patn 0 <> c) ->
  Zlength patn - (last + 1) < p.
Proof.
  intros patn p last c [Hp Hperiod] Hl He Hlatest.
  destruct (Z_lt_ge_dec (last + p) (Zlength patn)); [|lia].
  specialize (Hperiod last ltac:(lia) ltac:(lia)).
  specialize (Hlatest (last+p) ltac:(lia)). congruence.
Qed.

Lemma matched_range_memory_sublist : forall text patn pos memory,
  0 <= pos -> pos + memory <= Zlength text -> 0 <= memory <= Zlength patn ->
  strstr_rel_lib.matched_range text patn pos 0 memory ->
  sublist 0 memory patn = sublist pos (pos + memory) text.
Proof.
  intros text patn pos memory Hp Hw Hm Hmatch.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite !Zlength_sublist by lia; lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia.
    replace (i+0) with i by lia. replace (i+pos) with (pos+i) by lia.
    symmetry. apply Hmatch; lia.
Qed.

Lemma musl_periodic_memory_skip : forall text patn bits entries pos p memory remembered last,
  nonzero_bytes text -> 0 < p <= Zlength patn ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  strstr_rel_lib.matched_range text patn pos 0 memory ->
  periodic_memory_state patn p memory remembered ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= last < Zlength patn ->
  Znth last patn 0 = Znth (pos + Zlength patn - 1) text 0 ->
  (forall t, last < t < Zlength patn -> Znth t patn 0 <> Znth (pos + Zlength patn - 1) text 0) ->
  0 < Zlength patn - (last+1) < memory -> valid_skip text patn pos memory.
Proof.
  intros text patn bits entries pos p memory remembered last
    Htext Hp Hpos Hw Hmatched [Hm [Hr Hperiod]] Hb Hs Hl He Hlatest Hd.
  assert (Hmem : memory = Zlength patn - p) by (destruct Hm; destruct Hr; lia).
  assert (Hremembered : remembered <> 0) by (destruct Hm; lia).
  specialize (Hperiod Hremembered).
  assert (Hdist : Zlength patn - (last+1) < p).
  { eapply last_occurrence_period_distance; eauto. }
  assert (Hlookup : Znth (Znth (pos + Zlength patn - 1) text 0)
      (musl_distance_table patn bits entries) 0 = Zlength patn - (last+1)).
  { assert (Hc : 0 <= Znth (pos + Zlength patn - 1) text 0 < 256).
    { apply (nonzero_bytes_range text Htext); lia. }
    rewrite musl_distance_table_lookup by exact Hc. unfold musl_distance.
    assert (Hhit : Z.testbit (Znth (Znth (pos + Zlength patn - 1) text 0 / 64) bits 0)
       (Znth (pos + Zlength patn - 1) text 0 mod 64) = true).
    { apply (Hb _ Hc). exists last; auto. }
    rewrite Hhit. rewrite (Hs _ last Hc Hl He Hlatest). reflexivity. }
  rewrite Hmem.
  eapply (long_needle_periodic_memory_skip_valid text patn pos 0 p memory
      (musl_distance_table patn bits entries)); try lia.
  - unfold repetitive_split. rewrite !Zsublist_nil by lia; reflexivity.
  - split; [exact Hperiod|]. split; [auto|].
    apply matched_range_memory_sublist; auto; lia.
  - apply musl_table_sound; auto; try lia. apply nonzero_bytes_range; assumption.
Qed.

Lemma musl_periodic_memory_skip_before : forall text patn bits entries pos p memory remembered last,
  nonzero_bytes text -> 0 < p <= Zlength patn ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  strstr_rel_lib.matched_range text patn pos 0 memory ->
  periodic_memory_state patn p memory remembered ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= last < Zlength patn ->
  Znth last patn 0 = Znth (pos + Zlength patn - 1) text 0 ->
  (forall t, last < t < Zlength patn -> Znth t patn 0 <> Znth (pos + Zlength patn - 1) text 0) ->
  0 < Zlength patn - (last+1) < memory ->
  no_match_before text patn pos -> no_match_before text patn (pos + memory).
Proof.
  intros. eapply valid_skip_no_match_before; eauto.
  eapply musl_periodic_memory_skip; eauto.
Qed.

Lemma musl_periodic_memory_continuation : forall text patn bits entries pos cut p memory remembered last X,
  nonzero_bytes text -> 0 < p <= Zlength patn ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  strstr_rel_lib.matched_range text patn pos 0 memory ->
  periodic_memory_state patn p memory remembered ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= last < Zlength patn ->
  Znth last patn 0 = Znth (pos + Zlength patn - 1) text 0 ->
  (forall t, last < t < Zlength patn -> Znth t patn 0 <> Znth (pos + Zlength patn - 1) text 0) ->
  0 < Zlength patn - (last+1) < memory ->
  safeExec ATrue (generic_match_periodic_from text patn cut p pos memory) X ->
  safeExec ATrue (generic_match_periodic_from text patn cut p (pos+memory) 0) X.
Proof.
  intros. eapply generic_periodic_valid_skip_continuation; eauto.
  eapply musl_periodic_memory_skip; eauto.
Qed.
