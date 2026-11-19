From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib two_way_match_long_needle.
Local Open Scope Z_scope.

(* Untouched C entries are not consulted: a clear bit supplies the default. *)
Definition musl_distance (patn bits entries : list Z) (c : Z) :=
  if Z.testbit (Znth (c / 64) bits 0) (c mod 64)
  then Zlength patn - Znth c entries 0 else Zlength patn.
Definition musl_distance_table patn bits entries : list Z :=
  map (fun c => musl_distance patn bits entries (Z.of_nat c)) (seq 0 256).

Lemma musl_distance_table_length : forall patn bits entries,
  Zlength (musl_distance_table patn bits entries) = 256.
Proof. intros; unfold musl_distance_table; rewrite Zlength_map, Zlength_correct, length_seq; reflexivity. Qed.

Lemma musl_distance_table_lookup : forall patn bits entries c,
  0 <= c < 256 ->
  Znth c (musl_distance_table patn bits entries) 0 = musl_distance patn bits entries c.
Proof.
  intros patn bits entries c Hc. unfold musl_distance_table.
  rewrite (Znth_map _ _ _ 0%nat) by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma musl_table_prefix : forall patn upto bits entries,
  0 <= upto <= Zlength patn ->
  byteset_prefix patn upto bits -> shift_prefix patn upto entries ->
  shift_table_build_prefix patn upto (musl_distance_table patn bits entries).
Proof.
  intros patn upto bits entries Hu Hb Hs.
  split; [exact Hu|]. split; [apply musl_distance_table_length|].
  intros c Hc. rewrite musl_distance_table_lookup by assumption.
  unfold musl_distance.
  destruct (Z.testbit (Znth (c / 64) bits 0) (c mod 64)) eqn:Hbit.
  - destruct (shift_hit_last_stage12 patn upto bits entries c ltac:(lia) Hc Hb Hs Hbit)
      as [last [Hl [He [Hlater Hentry]]]].
    left. exists last. split; [exact (conj Hl (conj He Hlater))|]. rewrite Hentry; lia.
  - right. split; [|reflexivity]. intros j Hj He.
    assert (Htrue : Z.testbit (Znth (c / 64) bits 0) (c mod 64) = true).
    { apply (Hb c Hc). exists j; auto. } congruence.
Qed.

(* The original construction theorem supplies the next logical table. *)
Lemma musl_table_prefix_step : forall patn upto bits entries,
  0 <= upto < Zlength patn -> 0 <= Znth upto patn 0 < 256 ->
  byteset_prefix patn upto bits -> shift_prefix patn upto entries ->
  shift_table_build_prefix patn (upto + 1)
    (replace_Znth (Znth upto patn 0) (Zlength patn - upto - 1)
      (musl_distance_table patn bits entries)).
Proof.
  intros. apply shift_table_build_prefix_step; auto.
  apply musl_table_prefix; auto; lia.
Qed.

Lemma musl_table_sound : forall text patn bits entries,
  0 < Zlength patn ->
  (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
  byteset_prefix patn (Zlength patn) bits ->
  shift_prefix patn (Zlength patn) entries ->
  shift_table_sound text patn (musl_distance_table patn bits entries).
Proof.
  intros. apply shift_table_build_prefix_sound; auto.
  apply musl_table_prefix; auto; lia.
Qed.

Lemma musl_table_skip : forall text patn bits entries pos,
  0 < Zlength patn ->
  (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
  byteset_prefix patn (Zlength patn) bits ->
  shift_prefix patn (Zlength patn) entries ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  let d := musl_distance patn bits entries (Znth (pos + Zlength patn - 1) text 0) in
  (d = 0 /\ match_cond text patn pos (Zlength patn - 1)) \/ valid_skip text patn pos d.
Proof.
  intros text patn bits entries pos Hn Hr Hb Hs Hp Hw.
  destruct (musl_table_sound text patn bits entries Hn Hr Hb Hs) as [_ Hsound].
  apply Hsound; [auto|]. symmetry. apply musl_distance_table_lookup. apply Hr; lia.
Qed.

Lemma valid_skip_no_match_before : forall text patn pos d,
  valid_skip text patn pos d ->
  no_match_before text patn pos -> no_match_before text patn (pos + d).
Proof.
  intros text patn pos d [_ [_ Hskip]] Hbefore j Hj.
  destruct (Z_lt_ge_dec j pos); [apply Hbefore; lia|].
  intros [_ [_ Hmatch]]. apply (Hskip j ltac:(lia)); exact Hmatch.
Qed.

Lemma nonzero_bytes_range : forall text,
  nonzero_bytes text -> forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256.
Proof.
  intros text H i Hi. unfold nonzero_bytes in H. rewrite Forall_forall in H.
  assert (Hin : In (Znth i text 0) text).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hi; lia. }
  specialize (H _ Hin); lia.
Qed.

Lemma musl_table_skip_before : forall text patn bits entries pos d,
  nonzero_bytes text -> 0 < Zlength patn ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  d = musl_distance patn bits entries (Znth (pos + Zlength patn - 1) text 0) ->
  0 < d -> no_match_before text patn pos -> no_match_before text patn (pos + d).
Proof.
  intros text patn bits entries pos d Htext Hn Hb Hs Hp Hw Hd Hpos Hbefore.
  destruct (musl_table_skip text patn bits entries pos Hn
    (nonzero_bytes_range text Htext) Hb Hs Hp Hw) as [[Hz _]|Hskip].
  - lia.
  - eapply valid_skip_no_match_before; [rewrite Hd; exact Hskip|exact Hbefore].
Qed.

Lemma shift_table_prefix_unique : forall patn upto t1 t2,
  shift_table_build_prefix patn upto t1 ->
  shift_table_build_prefix patn upto t2 -> t1 = t2.
Proof.
  intros patn upto t1 t2 [_ [Hl1 H1]] [_ [Hl2 H2]].
  apply (proj2 (list_eq_ext t1 t2 0)). split; [lia|].
  intros c Hc. rewrite Hl1 in Hc.
  specialize (H1 c Hc). specialize (H2 c Hc).
  destruct H1 as [[i [[Hi [Hei Hli]] Hvi]]|[Hni Hvi]];
  destruct H2 as [[j [[Hj [Hej Hlj]] Hvj]]|[Hnj Hvj]].
  - assert (i = j).
    { destruct (Z_lt_ge_dec i j); [specialize (Hli j ltac:(lia)); congruence|].
      destruct (Z_lt_ge_dec j i); [specialize (Hlj i ltac:(lia)); congruence|lia]. }
    lia.
  - specialize (Hnj i Hi); congruence.
  - specialize (Hni j Hj); congruence.
  - congruence.
Qed.

Lemma musl_table_update : forall patn upto bits entries,
  0 <= upto < Zlength patn -> 0 <= Znth upto patn 0 < 256 ->
  Zlength bits = 4 -> Zlength entries = 256 ->
  byteset_prefix patn upto bits -> shift_prefix patn upto entries ->
  let c := Znth upto patn 0 in
  musl_distance_table patn
    (replace_Znth (c / 64) (Z.lor (Znth (c / 64) bits 0)
      ((Z.shiftl 1 (c mod 64)) mod (2 ^ 64))) bits)
    (replace_Znth c (upto + 1) entries) =
  replace_Znth c (Zlength patn - upto - 1) (musl_distance_table patn bits entries).
Proof.
  intros patn upto bits entries Hu Hc Hbl Hsl Hb Hs; cbn zeta.
  eapply shift_table_prefix_unique with (upto := upto + 1).
  - apply musl_table_prefix; [lia| |].
    + eapply byteset_prefix_step__twoway_table_1; eauto.
    + eapply shift_prefix_step__twoway_table_1; eauto.
  - apply musl_table_prefix_step; assumption.
Qed.

(* A table-selected positive distance is an allowed nondeterministic action. *)
Lemma generic_valid_skip_continuation : forall text patn cut period pos d X,
  pos + Zlength patn <= Zlength text -> valid_skip text patn pos d ->
  safeExec ATrue (generic_match_from text patn cut period pos) X ->
  safeExec ATrue (generic_match_from text patn cut period (pos + d)) X.
Proof.
  intros text patn cut period pos d X Hw Hskip Hexec.
  unfold generic_match_from in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold generic_match_loop_body in Hexec at 1. prog_nf in Hexec.
  safe_choice_l Hexec.
  prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ d) in Hexec.
  safe_step Hexec. unfold continue in Hexec. prog_nf in Hexec.
  unfold generic_match_from. exact Hexec.
Qed.

Lemma generic_periodic_valid_skip_continuation : forall text patn cut period pos memory d X,
  pos + Zlength patn <= Zlength text -> valid_skip text patn pos d ->
  safeExec ATrue (generic_match_periodic_from text patn cut period pos memory) X ->
  safeExec ATrue (generic_match_periodic_from text patn cut period (pos + d) 0) X.
Proof.
  intros text patn cut period pos memory d X Hw Hskip Hexec.
  unfold generic_match_periodic_from in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold generic_match_periodic_loop_body in Hexec at 1. prog_nf in Hexec.
  safe_choice_l Hexec.
  prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ d) in Hexec.
  safe_step Hexec. unfold continue in Hexec. prog_nf in Hexec.
  unfold generic_match_periodic_from. exact Hexec.
Qed.

Lemma musl_table_valid_skip : forall text patn bits entries pos d,
  0 < Zlength patn ->
  (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  d = musl_distance patn bits entries (Znth (pos + Zlength patn - 1) text 0) ->
  0 < d -> valid_skip text patn pos d.
Proof.
  intros text patn bits entries pos d Hn Hr Hb Hs Hp Hw Hd Hdpos.
  destruct (musl_table_skip text patn bits entries pos Hn Hr Hb Hs Hp Hw)
    as [[Hz _]|Hskip]; [lia|rewrite Hd; exact Hskip].
Qed.

Lemma musl_table_generic_continuation : forall text patn bits entries cut period pos d X,
  0 < Zlength patn ->
  (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  d = musl_distance patn bits entries (Znth (pos + Zlength patn - 1) text 0) ->
  0 < d -> safeExec ATrue (generic_match_from text patn cut period pos) X ->
  safeExec ATrue (generic_match_from text patn cut period (pos + d)) X.
Proof.
  intros. eapply generic_valid_skip_continuation; eauto.
  eapply musl_table_valid_skip; eauto.
Qed.

Lemma musl_table_periodic_continuation : forall text patn bits entries cut period pos memory d X,
  0 < Zlength patn ->
  (forall i, 0 <= i < Zlength text -> 0 <= Znth i text 0 < 256) ->
  byteset_prefix patn (Zlength patn) bits -> shift_prefix patn (Zlength patn) entries ->
  0 <= pos -> pos + Zlength patn <= Zlength text ->
  d = musl_distance patn bits entries (Znth (pos + Zlength patn - 1) text 0) ->
  0 < d -> safeExec ATrue (generic_match_periodic_from text patn cut period pos memory) X ->
  safeExec ATrue (generic_match_periodic_from text patn cut period (pos + d) 0) X.
Proof.
  intros. eapply generic_periodic_valid_skip_continuation; eauto.
  eapply musl_table_valid_skip; eauto.
Qed.
