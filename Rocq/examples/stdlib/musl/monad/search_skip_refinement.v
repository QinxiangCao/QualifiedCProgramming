From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib two_way_list_lemmas two_way_critical_factorization_theorem
  two_way_match strstr_result_bridge shift_table_refinement.
Local Open Scope Z_scope.

Lemma current_critical_factorization : forall patn cut p,
  critical_search_split patn cut p -> critical_factorization_prop patn cut p.
Proof.
  intros patn cut p [[mp [[Hper Hleast] [Hcut [Hp Hlocal]]]]
    [mp' [[Hper' Hleast'] [Hlocal' Hmin]]]].
  assert (mp=mp') by (specialize (Hleast mp' Hper'); specialize (Hleast' mp Hper); lia).
  subst mp'. constructor. exists mp. split.
  - split; [exact Hper|]. intros q Hq. specialize (Hleast q Hq); lia.
  - split; [exact Hcut|]. split; [exact Hp|].
    split; [exact Hlocal|]. intros q Hq. specialize (Hmin q Hq); lia.
Qed.

Lemma current_match_inv : forall text patn pos,
  patn <> nil -> 0 <= pos -> no_match_before text patn pos -> match_inv text patn pos.
Proof.
  intros text patn pos Hn Hp Hb. constructor; [exact Hp|].
  intros j Hj He. apply (Hb j Hj).
  pose proof (nonempty_sublist_match_bounds text patn j Hn He); unfold substring_at; tauto.
Qed.

Lemma original_match_inv_before : forall text patn pos,
  match_inv text patn pos -> no_match_before text patn pos.
Proof.
  intros text patn pos [_ Hbefore] j Hj [_ [_ He]]. exact (Hbefore j Hj He).
Qed.

Lemma current_matched_sublist : forall text patn pos lo hi,
  0 <= pos -> 0 <= lo <= hi -> hi <= Zlength patn -> pos+hi <= Zlength text ->
  strstr_rel_lib.matched_range text patn pos lo hi ->
  sublist lo hi patn = sublist (pos+lo) (pos+hi) text.
Proof.
  intros text patn pos lo hi Hp Hr Hn Ht Hm.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite !Zlength_sublist by lia; lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia.
    replace (i+(pos+lo)) with (pos+(i+lo)) by lia.
    symmetry; apply Hm; lia.
Qed.

Lemma original_right_mismatch_skip : forall text patn pos cut p memory k,
  no_match_before text patn pos -> 0 <= pos ->
  pos + Zlength patn <= Zlength text ->
  0 <= cut <= k -> k < Zlength patn -> 0 <= memory ->
  strstr_rel_lib.matched_range text patn pos 0 memory ->
  right_half_matched text patn pos cut memory k ->
  Znth k patn 0 <> Znth (pos+k) text 0 ->
  critical_search_split patn cut p ->
  no_match_before text patn (pos+k-cut+1).
Proof.
  intros text patn pos cut p memory k Hb Hp Hw Hcut Hk Hmem Hprefix [Hstart Hright] Hneq Hcf.
  assert (Hn : patn <> nil) by (intro He; subst patn; rewrite Zlength_nil in Hk; lia).
  apply original_match_inv_before.
  apply (match_inv_continue_right text patn cut p pos k).
  - apply current_critical_factorization; exact Hcf.
  - apply current_match_inv; assumption.
  - exact Hw.
  - constructor; [lia| |right; exact Hneq].
    apply current_matched_sublist; try lia.
    intros i Hi. destruct (Z_lt_ge_dec i memory).
    + apply Hprefix; lia.
    + apply Hright; lia.
  - exact Hk.
Qed.

Lemma original_left_mismatch_skip : forall text patn pos cut p memory k,
  no_match_before text patn pos -> 0 <= pos ->
  pos + Zlength patn <= Zlength text ->
  0 <= memory < k -> k <= cut -> k <= Zlength patn ->
  strstr_rel_lib.matched_range text patn pos k (Zlength patn) ->
  Znth (k-1) patn 0 <> Znth (pos+k-1) text 0 ->
  critical_search_split patn cut p ->
  no_match_before text patn (pos+p).
Proof.
  intros text patn pos cut p memory k Hb Hp Hw Hmem Hkc Hkn Hmatch Hneq Hcf.
  assert (Hn : patn <> nil) by (intro He; subst patn; rewrite Zlength_nil in Hkn; lia).
  assert (Hcut : 0 <= cut <= Zlength patn).
  { apply (proj1 (critical_factorization_bounds patn Hn cut p
      (current_critical_factorization patn cut p Hcf))).
  }
  apply original_match_inv_before.
  eapply (match_inv_continue_left text patn Hn cut p pos (k-1)); try lia.
  - apply current_critical_factorization; exact Hcf.
  - apply current_match_inv; assumption.
  - constructor; [lia| |left; lia].
    apply current_matched_sublist; try lia. unfold strstr_rel_lib.matched_range in *; intros; apply Hmatch; lia.
  - constructor; [lia| |right; replace (pos+(k-1)) with (pos+k-1) by lia; exact Hneq].
    replace (k-1+1) with k by lia.
    replace (pos+(k-1)+1) with (pos+k) by lia.
    apply current_matched_sublist; try lia. unfold strstr_rel_lib.matched_range in *; intros; apply Hmatch; lia.
Qed.

(* The original model's nondeterministic branch accepts musl's smaller
   nonperiodic step as well; the C period need not equal its default step. *)
Lemma original_left_mismatch_valid_skip : forall text patn pos cut p memory k,
  no_match_before text patn pos -> 0 <= pos ->
  pos + Zlength patn <= Zlength text -> pos+p <= Zlength text ->
  0 <= memory < k -> k <= cut -> k <= Zlength patn ->
  strstr_rel_lib.matched_range text patn pos k (Zlength patn) ->
  Znth (k-1) patn 0 <> Znth (pos+k-1) text 0 ->
  critical_search_split patn cut p -> valid_skip text patn pos p.
Proof.
  intros text patn pos cut p memory k Hb Hp Hw Hend Hmem Hkc Hkn Hmatch Hneq Hcf.
  assert (Hn : patn <> nil) by (intro He; subst patn; rewrite Zlength_nil in Hkn; lia).
  pose proof (original_left_mismatch_skip text patn pos cut p memory k
    Hb Hp Hw Hmem Hkc Hkn Hmatch Hneq Hcf) as Hbefore.
  destruct (critical_factorization_bounds patn Hn cut p
    (current_critical_factorization patn cut p Hcf)) as [_ Hpositive].
  split; [exact Hpositive|]. split; [exact Hend|]. intros j Hj He.
  apply (Hbefore j ltac:(lia)).
  pose proof (nonempty_sublist_match_bounds text patn j Hn He); unfold substring_at; tauto.
Qed.
