From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib two_way_list_lemmas two_way_critical_factorization_theorem
  factorization_refinement.
Local Open Scope Z_scope.

Lemma monad_critical_search_split patn cut p :
  critical_factorization_prop patn cut p ->
  strstr_rel_lib.critical_search_split patn cut p.
Proof.
  intros [[mp [Hglobal [Hcut [Hp [Hlocal Hminimal]]]]]].
  assert (Hleast : least_string_period patn mp).
  { destruct Hglobal as [Hper Hmin]. split; [exact Hper|].
    intros q Hq. specialize (Hmin q Hq). lia. }
  split.
  - exists mp. split; [exact Hleast|].
    split; [exact Hcut|]. split; [exact Hp|exact Hlocal].
  - exists mp. split; [exact Hleast|]. split; [exact Hlocal|].
    intros q Hq. specialize (Hminimal q Hq). lia.
Qed.

Lemma factorization_done_search_split patn cut p :
  patn <> nil -> factorization_done patn cut p ->
  strstr_rel_lib.critical_search_split patn cut p.
Proof.
  intros Hne Href. apply monad_critical_search_split.
  exact (proj1 (factorization_done_match_sound _ _ _ Hne Href)).
Qed.

Lemma factorization_done_nonrep_search_split patn cut p :
  patn <> nil -> factorization_done patn cut p ->
  sublist 0 cut patn <> sublist p (cut+p) patn ->
  strstr_rel_lib.critical_search_split patn cut
    (Z.max cut (Zlength patn-cut)+1).
Proof.
  intros Hne Href Hnonrep. apply monad_critical_search_split.
  apply (proj2 (factorization_done_match_sound _ _ _ Hne Href)). exact Hnonrep.
Qed.

Lemma factorization_done_cut_search_split patn cut p :
  patn <> nil -> factorization_done patn cut p -> 0 < cut ->
  strstr_rel_lib.critical_search_split patn cut cut.
Proof.
  intros Hne Href Hpos.
  destruct (factorization_done_search_split _ _ _ Hne Href)
    as [[mp [Hleast [Hcut [Hp Hlocal]]]] Hminimal].
  split; [|exact Hminimal].
  exists mp. split; [exact Hleast|]. split; [exact Hcut|].
  split; [lia|exact Hlocal].
Qed.
